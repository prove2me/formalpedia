-- Prove2me | solution 1 for M4aHerbrand.exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/17a08ca8-7b64-512c-81e8-c5ba0435919f

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_NumberField_PlaceDecomp_smul_algebraMap
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp Pointwise

@[elab_as_elim]
private theorem adicCompletion_induction_on {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {u : IsDedekindDomain.HeightOneSpectrum R}
    {p : u.adicCompletion K → Prop}
    (x : u.adicCompletion K) (hp : IsClosed {x | p x}) (ih : ∀ k : WithVal (u.valuation K), p k) : p x := by
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K u x
  exact UniformSpace.Completion.induction_on
    (p := fun y => p (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y)) y
    (hp.preimage (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K u)) ih

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff principalIdeles idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq"
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

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff principalIdeles idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq"
namespace ArtInv
p2m_open "M4aHerbrand"

section decompAux
open scoped Pointwise
variable (E F : Type*) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

theorem hzp_smul_valuationSubring_le (σ : F ≃ₐ[E] F) (hσ : σ • w.asIdeal = w.asIdeal) :
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

theorem hzp_mem_decomp_of_smul_asIdeal_eq (σ : F ≃ₐ[E] F) (hσ : σ • w.asIdeal = w.asIdeal) :
    σ ∈ NumberField.PlaceDecomp.decomp E F w := by
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm (hzp_smul_valuationSubring_le E F w σ hσ)
  rw [ValuationSubring.subset_pointwise_smul_iff]
  apply hzp_smul_valuationSubring_le E F w σ⁻¹
  rw [← hσ, inv_smul_smul]
  exact hσ.symm

end decompAux

theorem pow_smul_sub_pow_pow_mem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
    [MulSemiringAction G S] [SMulCommClass G R S] {Q : Ideal S} [Q.IsPrime] {φ : G} (hφ : IsArithFrobAt R φ Q) (i : ℕ) (y : S) :
    φ ^ i • y - y ^ Nat.card (R ⧸ Q.under R) ^ i ∈ Q := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hst := hφ.mem_stabilizer
    rw [pow_succ', mul_smul]
    have h1 : φ • (φ ^ i • y) - (φ ^ i • y) ^ Nat.card (R ⧸ Q.under R) ∈ Q := by
      have := hφ (φ ^ i • y)
      rwa [MulSemiringAction.toAlgHom_apply] at this
    have h2 : (φ ^ i • y) ^ Nat.card (R ⧸ Q.under R) - (y ^ Nat.card (R ⧸ Q.under R) ^ i) ^ Nat.card (R ⧸ Q.under R) ∈ Q :=
      Q.mem_of_dvd (sub_dvd_pow_sub_pow _ _ _) ih
    rw [← pow_mul, ← pow_succ] at h2
    have := Q.add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

attribute [local instance] Ideal.Quotient.field in

theorem zpowers_eq_decomp_of_isArithFrobAt_of_ramificationIdx_eq_one
    (E F' : Type) [Field E] [NumberField E] [Field F'] [NumberField F'] [Algebra E F'] [IsGalois E F']
    (w' : HeightOneSpectrum (𝓞 F'))
    (hunr : (w'.under (𝓞 E)).asIdeal.ramificationIdx' w'.asIdeal = 1)
    (φ' : F' ≃ₐ[E] F') (hφ' : IsArithFrobAt (𝓞 E) φ' w'.asIdeal) :
    ∃ hmem : φ' ∈ NumberField.PlaceDecomp.decomp E F' w',
      ∀ d : NumberField.PlaceDecomp.decomp E F' w', d ∈ Subgroup.zpowers (⟨φ', hmem⟩ : NumberField.PlaceDecomp.decomp E F' w') := by
  haveI : w'.asIdeal.IsPrime := w'.isPrime
  haveI : w'.asIdeal.IsMaximal := w'.isMaximal
  haveI : (w'.under (𝓞 E)).asIdeal.IsMaximal := (w'.under (𝓞 E)).isMaximal
  haveI : w'.asIdeal.LiesOver (w'.under (𝓞 E)).asIdeal := ⟨rfl⟩
  haveI : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite ℚ E F'
  haveI : Finite (F' ≃ₐ[E] F') := inferInstance
  have hmem : φ' ∈ NumberField.PlaceDecomp.decomp E F' w' := hzp_mem_decomp_of_smul_asIdeal_eq E F' w' φ' hφ'.mem_stabilizer
  refine ⟨hmem, ?_⟩

  letI : Fintype (𝓞 E ⧸ (w'.under (𝓞 E)).asIdeal) := Fintype.ofFinite _
  set N := Nat.card (𝓞 E ⧸ Ideal.under (𝓞 E) w'.asIdeal) with hN
  have hNq : Fintype.card (𝓞 E ⧸ (w'.under (𝓞 E)).asIdeal) = N := by
    show _ = Nat.card (𝓞 E ⧸ (w'.under (𝓞 E)).asIdeal)
    rw [Nat.card_eq_fintype_card]

  set Fr := FiniteField.frobeniusAlgHom (𝓞 E ⧸ (w'.under (𝓞 E)).asIdeal) (𝓞 F' ⧸ w'.asIdeal) with hFr
  have hordFr : orderOf Fr = (w'.under (𝓞 E)).asIdeal.inertiaDeg' w'.asIdeal := by
    rw [hFr, FiniteField.orderOf_frobeniusAlgHom, Ideal.inertiaDeg_algebraMap]

  set m := orderOf φ' with hm
  have hFrm : Fr ^ m = 1 := by
    apply DFunLike.ext
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [AlgHom.coe_pow, hFr, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply, hNq]
    show (Ideal.Quotient.mk w'.asIdeal y) ^ N ^ m = Ideal.Quotient.mk w'.asIdeal y
    have h := pow_smul_sub_pow_pow_mem hφ' m y
    rw [hm, pow_orderOf_eq_one, one_smul] at h
    rw [← map_pow, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h
  have hfm : (w'.under (𝓞 E)).asIdeal.inertiaDeg' w'.asIdeal ∣ m := by
    rw [← hordFr]
    exact orderOf_dvd_of_pow_eq_one hFrm

  have hcardD : Nat.card (NumberField.PlaceDecomp.decomp E F' w') = (w'.under (𝓞 E)).asIdeal.inertiaDeg' w'.asIdeal := by
    rw [NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg E F' w', hunr, one_mul]
  have hcardZ : Nat.card (Subgroup.zpowers (⟨φ', hmem⟩ : NumberField.PlaceDecomp.decomp E F' w')) = m := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
  have htop : Subgroup.zpowers (⟨φ', hmem⟩ : NumberField.PlaceDecomp.decomp E F' w') = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [hcardZ, hcardD]
    have hm0 : 0 < m := orderOf_pos φ'
    exact Nat.le_of_dvd hm0 hfm
  intro d
  rw [htop]
  exact Subgroup.mem_top d

theorem isArithFrobAt_restrictNormal
    (E F' K : Type) [Field E] [NumberField E] [Field F'] [NumberField F'] [Field K] [NumberField K]
    [Algebra E F'] [Algebra F' K] [Algebra E K] [IsScalarTower E F' K] [IsGalois E K] [IsGalois E F']
    (wK : HeightOneSpectrum (𝓞 K)) (φ : K ≃ₐ[E] K) (hφ : IsArithFrobAt (𝓞 E) φ wK.asIdeal) :
    IsArithFrobAt (𝓞 E) (φ.restrictNormal F') (wK.under (𝓞 F')).asIdeal := by
  intro x
  rw [MulSemiringAction.toAlgHom_apply]

  have hunder : Ideal.under (𝓞 E) (wK.under (𝓞 F')).asIdeal = Ideal.under (𝓞 E) wK.asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_under]
  rw [hunder, HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, map_sub, map_pow]
  have key := hφ (algebraMap (𝓞 F') (𝓞 K) x)
  rw [MulSemiringAction.toAlgHom_apply] at key
  have hcomm : algebraMap (𝓞 F') (𝓞 K) ((φ.restrictNormal F') • x) = φ • algebraMap (𝓞 F') (𝓞 K) x := by
    apply RingOfIntegers.coe_injective
    show algebraMap F' K ((φ.restrictNormal F') (x : F')) = φ (algebraMap F' K (x : F'))
    exact AlgEquiv.restrictNormal_commutes φ F' (x : F')
  rw [hcomm]
  exact key

theorem pow_natCard_decomp_eq_one_of_adjoin
    (E F F' K : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K] [NumberField K]
    [Algebra E F] [Algebra E F'] [Algebra F K] [Algebra F' K] [Algebra E K] [IsScalarTower E F K] [IsScalarTower E F' K]
    [IsGalois E K] [IsGalois E F] [IsGalois E F']
    (hgen : ∀ x : K, x ∈ Algebra.adjoin E (Set.range (algebraMap F K) ∪ Set.range (algebraMap F' K)))
    (wK : HeightOneSpectrum (𝓞 K))
    (ρ : NumberField.PlaceDecomp.decomp E K wK →* NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))
    (hρ : ∀ σ, ((ρ σ : NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))) : F ≃ₐ[E] F) = AlgEquiv.restrictNormalHom F (σ : K ≃ₐ[E] K))
    (ρ' : NumberField.PlaceDecomp.decomp E K wK →* NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F')))
    (hρ' : ∀ σ, ((ρ' σ : NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))) : F' ≃ₐ[E] F') = AlgEquiv.restrictNormalHom F' (σ : K ≃ₐ[E] K))
    (hdiv : Nat.card (NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))) ∣ Nat.card (NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F')))) :
    ∀ h : NumberField.PlaceDecomp.decomp E K wK, h ^ Nat.card (NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))) = 1 := by
  intro h
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite ℚ E F'
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  haveI : Finite (F' ≃ₐ[E] F') := inferInstance
  set n := Nat.card (NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))) with hn
  have h1 : (ρ h) ^ n = 1 := by
    obtain ⟨c, hc⟩ := hdiv
    rw [hc, pow_mul, pow_card_eq_one', one_pow]
  have h2 : (ρ' h) ^ n = 1 := pow_card_eq_one'
  have hF : AlgEquiv.restrictNormalHom F ((h ^ n : NumberField.PlaceDecomp.decomp E K wK) : K ≃ₐ[E] K) = 1 := by
    rw [← hρ, map_pow, h1]
    rfl
  have hF' : AlgEquiv.restrictNormalHom F' ((h ^ n : NumberField.PlaceDecomp.decomp E K wK) : K ≃ₐ[E] K) = 1 := by
    rw [← hρ', map_pow, h2]
    rfl
  apply Subtype.ext
  set σ : K ≃ₐ[E] K := ((h ^ n : NumberField.PlaceDecomp.decomp E K wK) : K ≃ₐ[E] K) with hσ
  show σ = 1
  apply AlgEquiv.ext
  intro x
  have hle : Algebra.adjoin E (Set.range (algebraMap F K) ∪ Set.range (algebraMap F' K)) ≤
      AlgHom.equalizer (σ : K →ₐ[E] K) (AlgHom.id E K) := by
    rw [Algebra.adjoin_le_iff]
    rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · show σ (algebraMap F K z) = algebraMap F K z
      rw [← AlgEquiv.restrictNormal_commutes]
      change algebraMap F K (AlgEquiv.restrictNormalHom F σ z) = _
      rw [hF, AlgEquiv.one_apply]
    · show σ (algebraMap F' K z) = algebraMap F' K z
      rw [← AlgEquiv.restrictNormal_commutes]
      change algebraMap F' K (AlgEquiv.restrictNormalHom F' σ z) = _
      rw [hF', AlgEquiv.one_apply]
  exact hle (hgen x)

end M4aHerbrand.ArtInv

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff principalIdeles idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq"
namespace ArtInvD45
p2m_open "M4aHerbrand"
open IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

section tower
variable (E L F : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F]

theorem adicCompletionSemialgHom_tower
    (v : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 L)) (hu : u.under (𝓞 E) = v)
    (w : HeightOneSpectrum (𝓞 F)) (hwu : w.under (𝓞 L) = u) (hw : w.under (𝓞 E) = v) (z : v.adicCompletion E) :
    Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) z =
      Extension.adicCompletionSemialgHom L F (⟨w, hwu⟩ : u.Extension (𝓞 F))
        (Extension.adicCompletionSemialgHom E L (⟨u, hu⟩ : v.Extension (𝓞 L)) z) := by
  induction z using adicCompletion_induction_on with
  | hp =>
    exact isClosed_eq (Extension.adicCompletionSemialgHom_continuous E F _)
      ((Extension.adicCompletionSemialgHom_continuous L F _).comp (Extension.adicCompletionSemialgHom_continuous E L _))
  | ih x =>
    rw [Extension.adicCompletionSemialgHom_coe, Extension.adicCompletionSemialgHom_coe, Extension.adicCompletionSemialgHom_coe]
    congr 2
    simp [← IsScalarTower.algebraMap_apply]
end tower

section action
variable (E L F : Type*) [Field E] [Field L] [Field F] [NumberField F] [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F]

omit [NumberField F] in
theorem restrictScalars_smul_valuationSubring (σ : F ≃ₐ[L] F) (S : ValuationSubring F) :
    (σ.restrictScalars E) • S = σ • S := by
  ext x
  simp only [ValuationSubring.mem_smul_pointwise_iff_exists]
  rfl

theorem mem_decomp_iff_restrictScalars_mem (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[L] F) :
    σ ∈ NumberField.PlaceDecomp.decomp L F w ↔ σ.restrictScalars E ∈ NumberField.PlaceDecomp.decomp E F w := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, restrictScalars_smul_valuationSubring]

theorem smul_eq_restrictScalars_smul (w : HeightOneSpectrum (𝓞 F)) (σ : NumberField.PlaceDecomp.decomp L F w)
    (z : w.adicCompletion F) :
    σ • z = (⟨(σ : F ≃ₐ[L] F).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E L F w σ).mp σ.2⟩ :
      NumberField.PlaceDecomp.decomp E F w) • z := by
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [NumberField.PlaceDecomp.actRingEquiv_apply, NumberField.PlaceDecomp.actRingEquiv_apply]
  rfl
end action

section bridgeval
variable (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (Φ : w.adicCompletion F ≃+* L')

theorem bv_le (y : w.adicCompletion F) : Valued.v y ≤ 1 ↔ ‖((Φ y : ↥L') : PadicAlgCl q)‖ ≤ 1 := by
  rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F w q L' Φ).1 y

omit [FiniteDimensional ℚ_[q] L'] in
theorem norm_coe_map_mul (y z : w.adicCompletion F) :
    ‖((Φ (y * z) : ↥L') : PadicAlgCl q)‖ = ‖((Φ y : ↥L') : PadicAlgCl q)‖ * ‖((Φ z : ↥L') : PadicAlgCl q)‖ := by
  rw [map_mul]; exact norm_mul _ _

omit [FiniteDimensional ℚ_[q] L'] in
theorem norm_coe_map_inv (y : w.adicCompletion F) :
    ‖((Φ y⁻¹ : ↥L') : PadicAlgCl q)‖ = ‖((Φ y : ↥L') : PadicAlgCl q)‖⁻¹ := by
  rw [map_inv₀]; exact norm_inv _

theorem bv_le₂ (y z : w.adicCompletion F) (hz : z ≠ 0) :
    Valued.v y ≤ Valued.v z ↔ ‖((Φ y : ↥L') : PadicAlgCl q)‖ ≤ ‖((Φ z : ↥L') : PadicAlgCl q)‖ := by
  have hz' : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
  have hzn : ‖((Φ z : ↥L') : PadicAlgCl q)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact_mod_cast (map_ne_zero Φ).mpr hz
  have key := bv_le F w q L' Φ (y * z⁻¹)
  rw [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.mpr hz'), one_mul, norm_coe_map_mul, norm_coe_map_inv,
    mul_inv_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) hzn.symm), one_mul] at key
  exact key

theorem bv_lt (y : w.adicCompletion F) : Valued.v y < 1 ↔ ‖((Φ y : ↥L') : PadicAlgCl q)‖ < 1 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h := bv_le₂ F w q L' Φ 1 y hy
    rw [map_one, map_one] at h
    simp only [OneMemClass.coe_one, norm_one] at h
    constructor
    · intro hlt; by_contra hge; exact (not_le.mpr hlt) (h.mpr (not_lt.mp hge))
    · intro hlt; by_contra hge; exact (not_le.mpr hlt) (h.mp (not_lt.mp hge))

theorem bv_lt₂ (y z : w.adicCompletion F) (hy : y ≠ 0) :
    Valued.v y < Valued.v z ↔ ‖((Φ y : ↥L') : PadicAlgCl q)‖ < ‖((Φ z : ↥L') : PadicAlgCl q)‖ := by
  have h := bv_le₂ F w q L' Φ z y hy
  constructor
  · intro hlt; by_contra hge; exact (not_le.mpr hlt) (h.mpr (not_lt.mp hge))
  · intro hlt; by_contra hge; exact (not_le.mpr hlt) (h.mp (not_lt.mp hge))

theorem bv_eq (y z : w.adicCompletion F) :
    Valued.v y = Valued.v z ↔ ‖((Φ y : ↥L') : PadicAlgCl q)‖ = ‖((Φ z : ↥L') : PadicAlgCl q)‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [map_zero, ZeroMemClass.coe_zero, norm_zero]
    have hzn : ‖((Φ z : ↥L') : PadicAlgCl q)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact_mod_cast (map_ne_zero Φ).mpr hz
    constructor
    · intro h; exact absurd ((Valuation.zero_iff _).mp h.symm) hz
    · intro h; exact absurd h.symm hzn
  rw [le_antisymm_iff, le_antisymm_iff, bv_le₂ F w q L' Φ y z hz, bv_le₂ F w q L' Φ z y hy]

end bridgeval

section frame
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (wK : HeightOneSpectrum (𝓞 K))
  (q : ℕ) [Fact q.Prime] (L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L'']
  [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K wK) L'']
  (Φ : wK.adicCompletion K ≃+* L'')
  (hΦ₃ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : wK.adicCompletion K), Φ (g • y) = g • Φ y)
  (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q))
  (hbase : ExtCitation.LocalLevel.IsBase q L'' ↥(NumberField.PlaceDecomp.decomp E K wK) K₀)

noncomputable abbrev ιK : (wK.under (𝓞 E)).adicCompletion E →+* wK.adicCompletion K :=
  (Extension.adicCompletionSemialgHom E K (⟨wK, rfl⟩ : (wK.under (𝓞 E)).Extension (𝓞 K)) :
    (wK.under (𝓞 E)).adicCompletion E →+* wK.adicCompletion K)

omit [FiniteDimensional ℚ_[q] L''] in
include hΦ₃ in

theorem smul_map_ιK (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (z : (wK.under (𝓞 E)).adicCompletion E) :
    g • Φ (ιK E K wK z) = Φ (ιK E K wK z) := by
  rw [← hΦ₃]
  congr 1
  exact (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E K wK _).mpr ⟨z, rfl⟩ g

noncomputable def toPadic : (wK.under (𝓞 E)).adicCompletion E →+* PadicAlgCl q :=
  (algebraMap (↥L'') (PadicAlgCl q)).comp ((Φ : wK.adicCompletion K →+* ↥L'').comp (ιK E K wK))

omit [FiniteDimensional ℚ_[q] L''] [IsGalois E K] [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K wK) L''] in
theorem toPadic_apply (z : (wK.under (𝓞 E)).adicCompletion E) : toPadic E K wK q L'' Φ z = ((Φ (ιK E K wK z) : ↥L'') : PadicAlgCl q) :=
  rfl

omit [FiniteDimensional ℚ_[q] L''] in
include hΦ₃ hbase in
theorem toPadic_mem (z : (wK.under (𝓞 E)).adicCompletion E) : toPadic E K wK q L'' Φ z ∈ K₀ :=
  (hbase.mem_iff _).mpr (fun g => smul_map_ιK E K wK q L'' Φ hΦ₃ g z)

noncomputable def baseBridge : (wK.under (𝓞 E)).adicCompletion E ≃+* ↥K₀ :=
  RingEquiv.ofBijective ((toPadic E K wK q L'' Φ).codRestrict K₀ (toPadic_mem E K wK q L'' Φ hΦ₃ K₀ hbase))
    ⟨fun z₁ z₂ h => by
      have h' := Subtype.ext_iff.mp h
      exact (toPadic E K wK q L'' Φ).injective h',
     fun x => by
      let xL : ↥L'' := ⟨(x : PadicAlgCl q), hbase.le x.2⟩
      have hfix : ∀ g : ↥(NumberField.PlaceDecomp.decomp E K wK), g • xL = xL := (hbase.mem_iff xL).mp x.2
      have hfix' : ∀ g : ↥(NumberField.PlaceDecomp.decomp E K wK), g • Φ.symm xL = Φ.symm xL := by
        intro g
        apply Φ.injective
        rw [hΦ₃, RingEquiv.apply_symm_apply, hfix]
      obtain ⟨z, hz⟩ := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E K wK _).mp hfix'
      refine ⟨z, Subtype.ext ?_⟩
      show ((Φ (ιK E K wK z) : ↥L'') : PadicAlgCl q) = x
      rw [show ιK E K wK z = Φ.symm xL from hz, RingEquiv.apply_symm_apply]⟩

omit [FiniteDimensional ℚ_[q] L''] in
theorem coe_baseBridge (z : (wK.under (𝓞 E)).adicCompletion E) :
    ((baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase z : ↥K₀) : PadicAlgCl q) = ((Φ (ιK E K wK z) : ↥L'') : PadicAlgCl q) :=
  rfl

omit [FiniteDimensional ℚ_[q] L''] in
theorem inclusion_baseBridge (z : (wK.under (𝓞 E)).adicCompletion E) :
    IntermediateField.inclusion hbase.le (baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase z) = Φ (ιK E K wK z) :=
  Subtype.ext rfl

variable [FiniteDimensional ℚ_[q] K₀]

omit [FiniteDimensional ℚ_[q] L''] in

theorem mem_integers_iff_baseBridge_mem_Rw (y : (wK.under (𝓞 E)).adicCompletion E) :
    y ∈ (wK.under (𝓞 E)).adicCompletionIntegers E ↔ baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase y ∈ ExtCitation.LocalLevel.Rw q K₀ := by
  rw [(NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv E
    (wK.under (𝓞 E)) q K₀ (baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase)).1 y]
  show _ ↔ ‖((baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase y : ↥K₀) : PadicAlgCl q)‖₊ ≤ 1
  rw [← coe_nnnorm, ← NNReal.coe_one, NNReal.coe_le_coe]

noncomputable def integersEquivRw : ↥((wK.under (𝓞 E)).adicCompletionIntegers E) ≃+* ↥(ExtCitation.LocalLevel.Rw q K₀) :=
  RingEquiv.ofBijective
    ((((baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase : (wK.under (𝓞 E)).adicCompletion E →+* ↥K₀)).comp
        ((wK.under (𝓞 E)).adicCompletionIntegers E).subtype).codRestrict (ExtCitation.LocalLevel.Rw q K₀)
      (fun y => (mem_integers_iff_baseBridge_mem_Rw E K wK q L'' Φ hΦ₃ K₀ hbase y).mp y.2))
    ⟨fun y₁ y₂ h => Subtype.ext ((baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase).injective (congrArg Subtype.val h)),
     fun x => by
      obtain ⟨y, hy⟩ := (baseBridge E K wK q L'' Φ hΦ₃ K₀ hbase).surjective x
      have hy' : y ∈ (wK.under (𝓞 E)).adicCompletionIntegers E :=
        (mem_integers_iff_baseBridge_mem_Rw E K wK q L'' Φ hΦ₃ K₀ hbase y).mpr (hy ▸ x.2)
      exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩⟩

omit [FiniteDimensional ℚ_[q] L''] in
include Φ hΦ₃ hbase in

theorem natCard_residueField_Rw :
    Nat.card (IsLocalRing.ResidueField ↥(ExtCitation.LocalLevel.Rw q K₀)) = Nat.card (𝓞 E ⧸ (wK.under (𝓞 E)).asIdeal) := by
  refine (Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv (integersEquivRw E K wK q L'' Φ hΦ₃ K₀ hbase)).toEquiv)).symm.trans ?_
  exact (Nat.card_congr (ResidueFieldEquivCompletionResidueField E (wK.under (𝓞 E))).toEquiv).symm

end frame

section frameB
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (wK : HeightOneSpectrum (𝓞 K))

omit [NumberField K] [IsGalois E K] in

theorem exists_uniformizer_base : ∃ ϖ : (wK.under (𝓞 E)).adicCompletion E, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer E (wK.under (𝓞 E))
  exact ⟨π, hπ⟩

omit [IsGalois E K] in

theorem valued_ιK_lt_one {ϖ : (wK.under (𝓞 E)).adicCompletion E} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    Valued.v (ιK E K wK ϖ) < 1 := by
  show Valued.v (Extension.adicCompletionSemialgHom E K (⟨wK, rfl⟩ : (wK.under (𝓞 E)).Extension (𝓞 K)) ϖ) < 1
  rw [Extension.valued_adicCompletionSemialgHom, hϖ]
  have hne := IsDedekindDomain.HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 E) (𝓞 K)
    (algebraMap_injective_of_field_isFractionRing (𝓞 E) (𝓞 K) E K) wK
  exact pow_lt_one' (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num) hne

theorem valued_smul_sub_pow_lt_one (φ : K ≃ₐ[E] K) (hφd : φ ∈ NumberField.PlaceDecomp.decomp E K wK)
    (hφ : IsArithFrobAt (𝓞 E) φ wK.asIdeal) (x₀ : wK.adicCompletion K) (hx₀ : Valued.v x₀ ≤ 1) :
    Valued.v ((⟨φ, hφd⟩ : NumberField.PlaceDecomp.decomp E K wK) • x₀ - x₀ ^ Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E))) < 1 := by
  let σ : NumberField.PlaceDecomp.decomp E K wK := ⟨φ, hφd⟩
  let 𝔪 : Ideal ↥(wK.adicCompletionIntegers K) := IsLocalRing.maximalIdeal _
  have hmem : ∀ t : ↥(wK.adicCompletionIntegers K), t ∈ 𝔪 ↔ Valued.v (t : wK.adicCompletion K) < 1 :=
    fun t => HeightOneSpectrum.mem_completionIdeal_iff K wK t

  let X : ↥(wK.adicCompletionIntegers K) := ⟨x₀, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K wK).mpr hx₀⟩
  obtain ⟨b, hb⟩ := HeightOneSpectrum.exists_adicValued_sub_lt_of_adicCompletionInteger K wK X 1
  let B : ↥(wK.adicCompletionIntegers K) := algebraMap (𝓞 K) ↥(wK.adicCompletionIntegers K) b
  have hBX : B - X ∈ 𝔪 := (hmem _).mpr hb

  have hσ𝔪 : ∀ t : ↥(wK.adicCompletionIntegers K), t ∈ 𝔪 → σ • t ∈ 𝔪 := by
    intro t ht
    rw [hmem] at ht ⊢
    rw [NumberField.PlaceDecomp.coe_smul_integers, NumberField.PlaceDecomp.valued_smul]
    exact ht

  have h1 : σ • X - σ • B ∈ 𝔪 := by
    rw [← smul_sub]
    apply hσ𝔪
    rw [← neg_sub]
    exact 𝔪.neg_mem hBX

  have h2 : σ • B - B ^ Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E)) ∈ 𝔪 := by
    have hglob := hφ b
    have hB : σ • B = algebraMap (𝓞 K) ↥(wK.adicCompletionIntegers K) (φ • b) := by
      apply Subtype.ext
      rw [NumberField.PlaceDecomp.coe_smul_integers]
      show σ • ((algebraMap (𝓞 K) K b : K) : wK.adicCompletion K) = ((algebraMap (𝓞 K) K (φ • b) : K) : wK.adicCompletion K)
      have := NumberField.PlaceDecomp.smul_algebraMap E K wK σ (algebraMap (𝓞 K) K b)
      rw [HeightOneSpectrum.algebraMap_adicCompletion] at this
      exact this
    rw [hB, ← map_pow, ← map_sub]
    have hover : wK.asIdeal = 𝔪.under (𝓞 K) := Ideal.LiesOver.over
    have hmap : ∀ t : 𝓞 K, t ∈ wK.asIdeal → algebraMap (𝓞 K) ↥(wK.adicCompletionIntegers K) t ∈ 𝔪 := by
      intro t ht
      have h' : t ∈ 𝔪.under (𝓞 K) := hover ▸ ht
      exact Ideal.mem_comap.mp h'
    exact hmap _ hglob

  have h3 : B ^ Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E)) - X ^ Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E)) ∈ 𝔪 := by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow B X (Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E)))
    rw [hc]
    exact 𝔪.mul_mem_right c hBX
  have htot : σ • X - X ^ Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E)) ∈ 𝔪 := by
    have := 𝔪.add_mem (𝔪.add_mem h1 h2) h3
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  have hfin := (hmem _).mp htot
  rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, NumberField.PlaceDecomp.coe_smul_integers] at hfin
  exact hfin

end frameB

section frameC
variable (E F' K : Type) [Field E] [NumberField E] [Field F'] [NumberField F'] [Field K] [NumberField K]
  [Algebra E F'] [Algebra F' K] [Algebra E K] [IsScalarTower E F' K] [IsGalois E K] [IsGalois E F']
  (wK : HeightOneSpectrum (𝓞 K))
  (ρ' : ↥(NumberField.PlaceDecomp.decomp E K wK) →* ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))))
  (hρ'surj : Function.Surjective ρ')
  (hρ'one : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ρ' σ = 1 ↔ ∀ x : F', (σ : K ≃ₐ[E] K) (algebraMap F' K x) = algebraMap F' K x)
  (hρ'lift : ∀ τ : ↥(NumberField.PlaceDecomp.decomp F' K wK), ∃ σ : ↥(NumberField.PlaceDecomp.decomp E K wK),
    (σ : K ≃ₐ[E] K) = AlgEquiv.restrictScalars E (τ : K ≃ₐ[F'] K) ∧ ρ' σ = 1)

omit [NumberField E] [IsScalarTower E F' K] [IsGalois E K] [IsGalois E F'] in
include hρ'surj in

theorem index_ker_eq : ρ'.ker.index = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))) := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ'surj, Subgroup.card_top]

omit [NumberField E] [IsScalarTower E F' K] [IsGalois E K] [IsGalois E F'] in

theorem forall_mem_zpowers_mk [IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E K wK)] (φ : ↥(NumberField.PlaceDecomp.decomp E K wK))
    (hgen : ∀ d : ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))), d ∈ Subgroup.zpowers (ρ' φ)) :
    ∀ c : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ'.ker, c ∈ Subgroup.zpowers (QuotientGroup.mk' ρ'.ker φ) := by
  intro c
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen (ρ' σ))
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  show (QuotientGroup.mk φ : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ MonoidHom.ker ρ') ^ i = QuotientGroup.mk σ
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, MonoidHom.mem_ker, map_mul ρ', map_inv ρ', map_zpow ρ', hi, inv_mul_cancel]

omit [NumberField E] [IsGalois E F'] in
include hρ'lift in

theorem mem_range_of_forall_ker_smul (y₀ : wK.adicCompletion K) (hy : ∀ h ∈ ρ'.ker, h • y₀ = y₀) :
    y₀ ∈ Set.range (Extension.adicCompletionSemialgHom F' K (⟨wK, rfl⟩ : (wK.under (𝓞 F')).Extension (𝓞 K))) := by
  haveI : IsGalois F' K := IsGalois.tower_top_of_isGalois E F' K
  refine (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom F' K wK y₀).mp fun τ => ?_
  obtain ⟨σ, hσ, hσ1⟩ := hρ'lift τ
  rw [smul_eq_restrictScalars_smul E F' K wK τ y₀]
  have heq : (⟨(τ : K ≃ₐ[F'] K).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E F' K wK τ).mp τ.2⟩ :
      ↥(NumberField.PlaceDecomp.decomp E K wK)) = σ := Subtype.ext hσ.symm
  rw [heq]
  exact hy σ hσ1

omit [IsGalois E F'] in
include hρ'lift in

theorem valued_le_of_forall_ker_smul
    (he' : ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal.ramificationIdx' (wK.under (𝓞 F')).asIdeal = 1)
    {ϖ : (wK.under (𝓞 E)).adicCompletion E} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (y₀ : wK.adicCompletion K) (hy : ∀ h ∈ ρ'.ker, h • y₀ = y₀) (hy1 : Valued.v y₀ < 1) :
    Valued.v y₀ ≤ Valued.v (ιK E K wK ϖ) := by
  obtain ⟨y₁, rfl⟩ := mem_range_of_forall_ker_smul E F' K wK ρ' hρ'lift y₀ hy
  have hLE : (wK.under (𝓞 F')).under (𝓞 E) = wK.under (𝓞 E) := by
    ext1
    simp [HeightOneSpectrum.under_asIdeal, Ideal.under_under]

  have hϖ' : Valued.v (Extension.adicCompletionSemialgHom E F' (⟨wK.under (𝓞 F'), hLE⟩ : (wK.under (𝓞 E)).Extension (𝓞 F')) ϖ) =
      WithZero.exp (-1 : ℤ) := by
    rw [Extension.valued_adicCompletionSemialgHom, hϖ]
    show WithZero.exp (-1 : ℤ) ^ ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal.ramificationIdx' (wK.under (𝓞 F')).asIdeal = _
    rw [he', pow_one]

  have hne := IsDedekindDomain.HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 F') (𝓞 K)
    (algebraMap_injective_of_field_isFractionRing (𝓞 F') (𝓞 K) F' K) wK
  have e1 := Extension.valued_adicCompletionSemialgHom F' K (⟨wK, rfl⟩ : (wK.under (𝓞 F')).Extension (𝓞 K)) y₁
  have e2 := Extension.valued_adicCompletionSemialgHom F' K (⟨wK, rfl⟩ : (wK.under (𝓞 F')).Extension (𝓞 K))
    (Extension.adicCompletionSemialgHom E F' (⟨wK.under (𝓞 F'), hLE⟩ : (wK.under (𝓞 E)).Extension (𝓞 F')) ϖ)
  have hy1e : Valued.v y₁ ^ (wK.under (𝓞 F')).asIdeal.ramificationIdx' wK.asIdeal < 1 := e1.symm.trans_lt hy1
  have hy1' : Valued.v y₁ < 1 := by
    by_contra h
    exact (not_le.mpr hy1e) (one_le_pow_of_one_le' (not_lt.mp h) _)
  have hy2 : Valued.v y₁ ≤ WithZero.exp (-1 : ℤ) := NumberField.PlaceDecomp.le_exp_neg_one_of_lt_one hy1'
  have htow := adicCompletionSemialgHom_tower E F' K (wK.under (𝓞 E)) (wK.under (𝓞 F')) hLE wK rfl rfl ϖ
  calc Valued.v (Extension.adicCompletionSemialgHom F' K (⟨wK, rfl⟩ : (wK.under (𝓞 F')).Extension (𝓞 K)) y₁)
      = Valued.v y₁ ^ (wK.under (𝓞 F')).asIdeal.ramificationIdx' wK.asIdeal := e1
    _ ≤ (WithZero.exp (-1 : ℤ)) ^ (wK.under (𝓞 F')).asIdeal.ramificationIdx' wK.asIdeal := pow_le_pow_left' hy2 _
    _ = Valued.v (Extension.adicCompletionSemialgHom F' K (⟨wK, rfl⟩ : (wK.under (𝓞 F')).Extension (𝓞 K))
          (Extension.adicCompletionSemialgHom E F' (⟨wK.under (𝓞 F'), hLE⟩ : (wK.under (𝓞 E)).Extension (𝓞 F')) ϖ)) := by
        rw [← hϖ']; exact e2.symm
    _ = Valued.v (ιK E K wK ϖ) := by rw [← htow]; rfl

omit [IsGalois E K] in
include hρ'one in
attribute [local instance] Ideal.Quotient.field in

theorem map_eq_one_of_mem_inertia
    (he' : ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal.ramificationIdx' (wK.under (𝓞 F')).asIdeal = 1)
    (τ : ↥(NumberField.PlaceDecomp.decomp E K wK)) (hτ : (τ : K ≃ₐ[E] K) ∈ wK.asIdeal.inertia (K ≃ₐ[E] K)) :
    ρ' τ = 1 := by
  classical

  set τ' : F' ≃ₐ[E] F' := (τ : K ≃ₐ[E] K).restrictNormal F' with hτ'
  have hτ'I : τ' ∈ (wK.under (𝓞 F')).asIdeal.inertia (F' ≃ₐ[E] F') := by
    intro x
    show τ' • x - x ∈ (wK.under (𝓞 F')).asIdeal
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_sub]
    have hx := hτ (algebraMap (𝓞 F') (𝓞 K) x)
    have hcomm : algebraMap (𝓞 F') (𝓞 K) (τ' • x) = (τ : K ≃ₐ[E] K) • algebraMap (𝓞 F') (𝓞 K) x := by
      apply Subtype.ext
      show algebraMap F' K (τ' (x : F')) = (τ : K ≃ₐ[E] K) (algebraMap F' K (x : F'))
      exact AlgEquiv.restrictNormal_commutes (τ : K ≃ₐ[E] K) F' (x : F')
    rw [hcomm]
    exact hx

  have hbot : (wK.under (𝓞 F')).asIdeal.inertia (F' ≃ₐ[E] F') = ⊥ := by
    haveI : (wK.under (𝓞 F')).asIdeal.LiesOver ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal := ⟨rfl⟩
    haveI : (wK.under (𝓞 F')).asIdeal.IsMaximal := (wK.under (𝓞 F')).isMaximal
    haveI : ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal.IsMaximal := ((wK.under (𝓞 F')).under (𝓞 E)).isMaximal
    haveI : Algebra.IsSeparable (𝓞 E ⧸ ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal) (𝓞 F' ⧸ (wK.under (𝓞 F')).asIdeal) :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    apply Subgroup.eq_bot_of_card_eq
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := F' ≃ₐ[E] F') ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal
        (wK.under (𝓞 F')).asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal (wK.under (𝓞 F')).asIdeal (F' ≃ₐ[E] F'),
      ← Ideal.ramificationIdx'_eq_ramificationIdx ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal (wK.under (𝓞 F')).asIdeal ((wK.under (𝓞 F')).under (𝓞 E)).ne_bot, he']
  rw [hbot, Subgroup.mem_bot] at hτ'I
  rw [hρ'one]
  intro x
  have h := AlgEquiv.restrictNormal_commutes (τ : K ≃ₐ[E] K) F' x
  rw [← hτ', hτ'I, AlgEquiv.one_apply] at h
  exact h.symm

end frameC

section main

scoped instance isMulCommutative_decomp (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K] [IsMulCommutative (K ≃ₐ[E] K)]
    (wK : HeightOneSpectrum (𝓞 K)) : IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E K wK) :=
  ⟨⟨fun a b => Subtype.ext (mul_comm (a : K ≃ₐ[E] K) (b : K ≃ₐ[E] K))⟩⟩

set_option maxHeartbeats 3200000 in

theorem D45
    (E F' K : Type) [Field E] [NumberField E] [Field F'] [NumberField F'] [Field K] [NumberField K]
    [Algebra E F'] [Algebra F' K] [Algebra E K] [IsScalarTower E F' K] [IsGalois E K] [IsGalois E F']
    [IsMulCommutative (K ≃ₐ[E] K)]
    (v : HeightOneSpectrum (𝓞 E)) (wK : HeightOneSpectrum (𝓞 K)) (hv : wK.under (𝓞 E) = v)

    (he' : ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal.ramificationIdx' (wK.under (𝓞 F')).asIdeal = 1)
    (ρ' : ↥(NumberField.PlaceDecomp.decomp E K wK) →* ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))))
    (hρ'surj : Function.Surjective ρ')
    (hρ'one : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ρ' σ = 1 ↔ ∀ x : F', (σ : K ≃ₐ[E] K) (algebraMap F' K x) = algebraMap F' K x)
    (hρ'lift : ∀ τ : ↥(NumberField.PlaceDecomp.decomp F' K wK), ∃ σ : ↥(NumberField.PlaceDecomp.decomp E K wK),
      (σ : K ≃ₐ[E] K) = AlgEquiv.restrictScalars E (τ : K ≃ₐ[F'] K) ∧ ρ' σ = 1)
    (φ : K ≃ₐ[E] K) (hφd : φ ∈ NumberField.PlaceDecomp.decomp E K wK) (hφ : IsArithFrobAt (𝓞 E) φ wK.asIdeal)
    (hgen' : ∀ d : ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))), d ∈ Subgroup.zpowers (ρ' ⟨φ, hφd⟩))
    (hexp' : ∀ h : ↥(NumberField.PlaceDecomp.decomp E K wK), h ^ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))) = 1)

    (q : ℕ) [Fact q.Prime] (L2 : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L2]
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K wK) L2] [FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K wK) L2]
    [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ]
    (Φ2 : wK.adicCompletion K ≃+* L2)
    (hΦ21 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L2 y = algebraMap ℚ_[q] L2 y)
    (hΦ22 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : (↥L2)ˣ), ((g • y : (↥L2)ˣ) : L2) = g • (y : L2))
    (hΦ23 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : wK.adicCompletion K), Φ2 (g • y) = g • Φ2 y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hbase2 : ExtCitation.LocalLevel.IsBase q L2 ↥(NumberField.PlaceDecomp.decomp E K wK) K₀)
    (u2 : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ))
    (hu2 : ExtCitation.LocalLevel.IsLocalFundamentalClass q L2 ↥(NumberField.PlaceDecomp.decomp E K wK) K₀ u2)

    (𝔣K : Ideal (𝓞 E)) (hadmK : NumberField.NormIndex.IsAdmissibleModulusOfDegree E K (Module.finrank E K) 𝔣K)
    (rK : (AdeleRing (𝓞 E) E)ˣ →* (K ≃ₐ[E] K))
    (hrK₁ : principalIdeles (𝓞 E) E ≤ rK.ker)
    (hrK₂ : rK.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E K).idelicNorm.range)
    (hrK₃ : Function.Surjective rK)
    (hrK₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣K u 1 →
      rK u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E K v ^ placeOrd E (projFin E u) v)

    (ιv : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ)
    (hιv : ∀ z, ιv z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hιv' : ∀ z, finPart v (ιv z) = z)
    (fE : (v.adicCompletion E)ˣ →* ↥(NumberField.PlaceDecomp.decomp E K wK))
    (hfE : ∀ z, ((fE z : ↥(NumberField.PlaceDecomp.decomp E K wK)) : K ≃ₐ[E] K) = rK (ιv z))

    (H' : Subgroup ↥(NumberField.PlaceDecomp.decomp E K wK)) (t : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ H')
    (ht : ∀ c, c ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (a : (v.adicCompletion E)ˣ) (b2 : (↥L2)ˣ)
    (hb2 : ((b2 : ↥L2) : PadicAlgCl q) =
      ((Φ2 (Extension.adicCompletionSemialgHom E K (⟨wK, hv⟩ : v.Extension (𝓞 K)) (a : v.adicCompletion E)) : ↥L2) : PadicAlgCl q))
    (hb2inv : (Additive.ofMul b2 : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).ρ.comp H'.subtype))
    (hca : carryFun t ht htfin (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants H')
        ⟨Additive.ofMul b2, hb2inv⟩ ∈
      cocycles₂ ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants H')) :
    ∃ m : ℕ, (QuotientGroup.mk (fE a) : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ H') = t ^ m ∧
      ((infNatTrans ℤ H' 2).app (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants H')).hom
            ⟨carryFun t ht htfin (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants H')
              ⟨Additive.ofMul b2, hb2inv⟩, hca⟩) =
        (m * Nat.card H') • u2 := by
  subst hv
  classical

  let Φ₀ := baseBridge E K wK q L2 Φ2 hΦ23 K₀ hbase2
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer_base E K wK
  have hιϖ : Valued.v (ιK E K wK ϖ) < 1 := valued_ιK_lt_one E K wK hϖ
  have hιϖ0 : ιK E K wK ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hιϖ
    have hϖ0 : ϖ ≠ 0 := by intro h0; rw [h0, map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
    exact hϖ0 ((map_eq_zero _).mp h)
  have hπ0 : Φ2 (ιK E K wK ϖ) ≠ 0 := (map_ne_zero Φ2).mpr hιϖ0
  let π : (↥L2)ˣ := Units.mk0 (Φ2 (ιK E K wK ϖ)) hπ0
  have hπval : ((π : (↥L2)ˣ) : ↥L2) = Φ2 (ιK E K wK ϖ) := rfl

  have hπH : ∀ h : ↥(NumberField.PlaceDecomp.decomp E K wK), h • π = π := fun h =>
    Units.ext (by rw [hΦ22, hπval]; exact smul_map_ιK E K wK q L2 Φ2 hΦ23 h ϖ)
  have hπ1 : ‖(((π : (↥L2)ˣ) : ↥L2) : PadicAlgCl q)‖ < 1 := (bv_lt K wK q L2 Φ2 _).mp hιϖ
  haveI hNn : (MonoidHom.ker ρ').Normal := inferInstance
  have hπmax : ∀ y : ↥L2, (∀ h ∈ MonoidHom.ker ρ', h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 →
      ‖(y : PadicAlgCl q)‖ ≤ ‖(((π : (↥L2)ˣ) : ↥L2) : PadicAlgCl q)‖ := by
    intro y hy hy1
    obtain ⟨y₀, rfl⟩ := Φ2.surjective y
    have hy₀ : ∀ h ∈ MonoidHom.ker ρ', h • y₀ = y₀ := fun h hh => Φ2.injective (by rw [hΦ23, hy h hh])
    have hv1 : Valued.v y₀ < 1 := (bv_lt K wK q L2 Φ2 y₀).mpr hy1
    have key := valued_le_of_forall_ker_smul E F' K wK ρ' hρ'lift he' hϖ y₀ hy₀ hv1
    exact (bv_le₂ K wK q L2 Φ2 y₀ _ hιϖ0).mp key
  have hzp := forall_mem_zpowers_mk E F' K wK ρ' ⟨φ, hφd⟩ hgen'
  have hN : Nat.card (IsLocalRing.ResidueField ↥(ExtCitation.LocalLevel.Rw q K₀)) = Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E)) :=
    natCard_residueField_Rw E K wK q L2 Φ2 hΦ23 K₀ hbase2
  have hfrob : ∀ x : ↥L2, (∀ h ∈ MonoidHom.ker ρ', h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖(((⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) • x : ↥L2) : PadicAlgCl q) -
        (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField ↥(ExtCitation.LocalLevel.Rw q K₀))‖ < 1 := by
    intro x _ hx1
    obtain ⟨x₀, rfl⟩ := Φ2.surjective x
    have hx₀ : Valued.v x₀ ≤ 1 := (bv_le K wK q L2 Φ2 x₀).mpr hx1
    have key := valued_smul_sub_pow_lt_one E K wK φ hφd hφ x₀ hx₀
    rw [hN, ← hΦ23]
    have hcoe : ((Φ2 ((⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) • x₀) : ↥L2) : PadicAlgCl q) -
        ((Φ2 x₀ : ↥L2) : PadicAlgCl q) ^ Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E)) =
        ((Φ2 ((⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) • x₀ - x₀ ^ Nat.card (𝓞 E ⧸ wK.asIdeal.under (𝓞 E))) : ↥L2) :
          PadicAlgCl q) := by
      rw [map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
    rw [hcoe]
    exact (bv_lt K wK q L2 Φ2 _).mp key
  have hexp : ∀ h : ↥(NumberField.PlaceDecomp.decomp E K wK), h ^ (MonoidHom.ker ρ').index = 1 := by
    intro h; rw [index_ker_eq E F' K wK ρ' hρ'surj]; exact hexp' h

  let f : (↥K₀)ˣ →* ↥(NumberField.PlaceDecomp.decomp E K wK) :=
    fE.comp (Units.map (Φ₀.symm : ↥K₀ ≃+* (wK.under (𝓞 E)).adicCompletion E).toRingHom.toMonoidHom)
  have hf : ∀ b : (↥K₀)ˣ, f b = fE (Units.map (Φ₀.symm : ↥K₀ ≃+* (wK.under (𝓞 E)).adicCompletion E).toRingHom.toMonoidHom b) :=
    fun b => rfl
  have hΦ₀b : ∀ b : (↥K₀)ˣ, Φ₀ ((Units.map (Φ₀.symm : ↥K₀ ≃+* (wK.under (𝓞 E)).adicCompletion E).toRingHom.toMonoidHom b :
      ((wK.under (𝓞 E)).adicCompletion E)ˣ) : (wK.under (𝓞 E)).adicCompletion E) = (b : ↥K₀) := fun b => Φ₀.apply_symm_apply _

  have h1 : ∀ (b : (↥K₀)ˣ) (k : ℤ), ‖((b : ↥K₀) : PadicAlgCl q)‖ = ‖(((π : (↥L2)ˣ) : ↥L2) : PadicAlgCl q)‖ ^ k →
      (QuotientGroup.mk (f b) : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ MonoidHom.ker ρ') =
        (QuotientGroup.mk (⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) : _ ⧸ MonoidHom.ker ρ') ^ k := by
    intro b k hk
    set zu : ((wK.under (𝓞 E)).adicCompletion E)ˣ :=
      Units.map (Φ₀.symm : ↥K₀ ≃+* (wK.under (𝓞 E)).adicCompletion E).toRingHom.toMonoidHom b with hzu

    have hpow : ((Φ₀ (ϖ ^ k) : ↥K₀) : PadicAlgCl q) = ((Φ₀ ϖ : ↥K₀) : PadicAlgCl q) ^ k := by
      rw [map_zpow₀]
      exact map_zpow₀ (algebraMap (↥K₀) (PadicAlgCl q)) _ _
    have hnπ : ‖(((π : (↥L2)ˣ) : ↥L2) : PadicAlgCl q)‖ = ‖((Φ₀ ϖ : ↥K₀) : PadicAlgCl q)‖ := rfl
    have heq : ‖((Φ₀ (zu : (wK.under (𝓞 E)).adicCompletion E) : ↥K₀) : PadicAlgCl q)‖ =
        ‖((Φ₀ (ϖ ^ k) : ↥K₀) : PadicAlgCl q)‖ := by
      rw [hΦ₀b, hk, hnπ, hpow, norm_zpow]
    have hv := (bv_eq E (wK.under (𝓞 E)) q K₀ Φ₀ (zu : (wK.under (𝓞 E)).adicCompletion E) (ϖ ^ k)).mpr heq
    have hval : Valued.v (zu : (wK.under (𝓞 E)).adicCompletion E) = WithZero.exp (-k) := by
      rw [hv, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

    have hord : placeOrd E (projFin E (ιv zu)) (wK.under (𝓞 E)) = k := by
      show -WithZero.log (Valued.v ((finPart (wK.under (𝓞 E)) (ιv zu) : ((wK.under (𝓞 E)).adicCompletion E)ˣ) :
        (wK.under (𝓞 E)).adicCompletion E)) = k
      rw [hιv', hval, WithZero.log_exp, neg_neg]

    have hI := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt E K 𝔣K hadmK rK hrK₁ hrK₂ hrK₃ hrK₄
      (wK.under (𝓞 E)) zu (ιv zu) (hιv zu) (hιv' zu) wK rfl φ hφ
    rw [hord] at hI
    have hτ : (((f b) * ((⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) ^ k)⁻¹ :
        ↥(NumberField.PlaceDecomp.decomp E K wK)) : K ≃ₐ[E] K) ∈ wK.asIdeal.inertia (K ≃ₐ[E] K) := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, SubgroupClass.coe_zpow, hf, hfE]
      exact hI

    have hker : ρ' ((f b) * ((⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) ^ k)⁻¹) = 1 :=
      map_eq_one_of_mem_inertia E F' K wK ρ' hρ'one he' _ hτ
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    have hrew : (f b)⁻¹ * (⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) ^ k =
        ((f b) * ((⟨φ, hφd⟩ : ↥(NumberField.PlaceDecomp.decomp E K wK)) ^ k)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hrew]
    exact Subgroup.inv_mem _ (MonoidHom.mem_ker.mpr hker)

  have h2 : ∀ (H'' : Subgroup ↥(NumberField.PlaceDecomp.decomp E K wK)) (b : (↥K₀)ˣ),
      (∃ c : (↥L2)ˣ, (∀ h ∈ H'', h • c = c) ∧
        ∏ᶠ d : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ H'', (Quotient.out d) • c =
          Units.map (IntermediateField.inclusion hbase2.le).toRingHom.toMonoidHom b) →
      f b ∈ H'' := by
    intro H'' b hb
    obtain ⟨c, hc, hprod⟩ := hb
    set zu : ((wK.under (𝓞 E)).adicCompletion E)ˣ :=
      Units.map (Φ₀.symm : ↥K₀ ≃+* (wK.under (𝓞 E)).adicCompletion E).toRingHom.toMonoidHom b with hzu
    let ψ : (↥L2)ˣ →* (wK.adicCompletion K)ˣ := Units.map (Φ2.symm : ↥L2 ≃+* wK.adicCompletion K).toRingHom.toMonoidHom
    have hψ : ∀ (h : ↥(NumberField.PlaceDecomp.decomp E K wK)) (u : (↥L2)ˣ), ψ (h • u) = h • ψ u := by
      intro h u
      apply Units.ext
      show Φ2.symm ((h • u : (↥L2)ˣ) : ↥L2) = h • Φ2.symm (u : ↥L2)
      rw [hΦ22]
      apply Φ2.injective
      rw [hΦ23, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    have hc₀ : ∀ h ∈ H'', h • ψ c = ψ c := fun h hh => by rw [← hψ, hc h hh]
    have hN₀ : (((∏ᶠ d : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ H'', (Quotient.out d) • ψ c : (wK.adicCompletion K)ˣ) :
          (wK.adicCompletion K)ˣ) : wK.adicCompletion K) =
        Extension.adicCompletionSemialgHom E K (⟨wK, rfl⟩ : (wK.under (𝓞 E)).Extension (𝓞 K))
          (zu : (wK.under (𝓞 E)).adicCompletion E) := by
      have hfin : ∏ᶠ d : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ H'', (Quotient.out d) • ψ c =
          ψ (∏ᶠ d : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ H'', (Quotient.out d) • c) := by
        rw [MonoidHom.map_finprod ψ (Set.toFinite _)]
        exact finprod_congr fun d => (hψ _ _).symm
      rw [hfin, hprod]
      show Φ2.symm ((Units.map (IntermediateField.inclusion hbase2.le).toRingHom.toMonoidHom b : (↥L2)ˣ) : ↥L2) = ιK E K wK zu
      apply Φ2.injective
      rw [RingEquiv.apply_symm_apply]
      show IntermediateField.inclusion hbase2.le (b : ↥K₀) = Φ2 (ιK E K wK zu)
      rw [← inclusion_baseBridge E K wK q L2 Φ2 hΦ23 K₀ hbase2 (zu : (wK.under (𝓞 E)).adicCompletion E), hΦ₀b]
    have hmem := M4aHerbrand.idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq E K 𝔣K hadmK rK hrK₁ hrK₂ hrK₃ hrK₄
      (wK.under (𝓞 E)) zu (ιv zu) (hιv zu) (hιv' zu) wK rfl H'' (ψ c) hc₀ hN₀
    obtain ⟨h, hh, hh'⟩ := Subgroup.mem_map.mp hmem
    have hfb : f b = h := Subtype.ext (by rw [hf, hfE]; exact hh'.symm)
    rw [hfb]
    exact hh

  set a' : (↥K₀)ˣ := Units.map (Φ₀ : (wK.under (𝓞 E)).adicCompletion E ≃+* ↥K₀).toRingHom.toMonoidHom a with ha'
  have hfa : f a' = fE a := by
    rw [hf]
    congr 1
    exact Units.ext (Φ₀.symm_apply_apply _)
  have hab : Units.map (IntermediateField.inclusion hbase2.le).toRingHom.toMonoidHom a' = b2 := by
    apply Units.ext
    apply Subtype.ext
    show ((IntermediateField.inclusion hbase2.le (Φ₀ (a : (wK.under (𝓞 E)).adicCompletion E)) : ↥L2) : PadicAlgCl q) =
      ((b2 : ↥L2) : PadicAlgCl q)
    rw [inclusion_baseBridge, hb2]
    rfl
  subst hab

  obtain ⟨m, hm⟩ : ∃ m : ℕ, (QuotientGroup.mk (f a') : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ H') = t ^ m := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (ht (QuotientGroup.mk (f a')))
    refine ⟨(i % (orderOf t : ℤ)).toNat, ?_⟩
    rw [← hi, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast htfin.orderOf_pos.ne')), zpow_mod_orderOf]
  refine ⟨m, by rw [← hfa]; exact hm, ?_⟩
  haveI : H'.Normal := inferInstance
  exact ExtCitation.LocalLevel.infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem q L2
    ↥(NumberField.PlaceDecomp.decomp E K wK) hΦ21 hΦ22 K₀ hbase2 u2 hu2 (MonoidHom.ker ρ') ⟨φ, hφd⟩ π hzp hfrob hπH hπ1 hπmax hexp
    f h1 h2 H' t ht htfin a' m hm hb2inv hca

end main

end M4aHerbrand.ArtInvD45
p2m_reactivate "P2MW.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer.M4aHerbrand P2MW.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer.M4aHerbrand.ArtInvD45"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer.M4aHerbrand"

open M4aHerbrand.ArtInvD45 in
set_option maxHeartbeats 3200000 in

theorem solution
    (E F F' K : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K] [NumberField K]
    [Algebra E F] [Algebra E F'] [Algebra F K] [Algebra F' K] [Algebra E K] [IsScalarTower E F K] [IsScalarTower E F' K]
    [IsGalois E K] [IsGalois E F] [IsGalois E F'] [IsMulCommutative (K ≃ₐ[E] K)]

    (hgen : ∀ x : K, x ∈ Algebra.adjoin E (Set.range (algebraMap F K) ∪ Set.range (algebraMap F' K)))

    (v : HeightOneSpectrum (𝓞 E)) (wK : HeightOneSpectrum (𝓞 K)) (hv : wK.under (𝓞 E) = v)
    [IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E K wK)]

    (ρ : ↥(NumberField.PlaceDecomp.decomp E K wK) →* ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))
    (hρres : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ((ρ σ : ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) : F ≃ₐ[E] F) =
      AlgEquiv.restrictNormalHom F (σ : K ≃ₐ[E] K))
    (ρ' : ↥(NumberField.PlaceDecomp.decomp E K wK) →* ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))))
    (hρ'surj : Function.Surjective ρ')
    (hρ'res : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ((ρ' σ : ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F')))) : F' ≃ₐ[E] F') =
      AlgEquiv.restrictNormalHom F' (σ : K ≃ₐ[E] K))
    (hρ'ker : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ρ' σ = 1 ↔ ∀ x : F', (σ : K ≃ₐ[E] K) (algebraMap F' K x) = algebraMap F' K x)
    (hρ'lift : ∀ τ : ↥(NumberField.PlaceDecomp.decomp F' K wK), ∃ σ : ↥(NumberField.PlaceDecomp.decomp E K wK),
      (σ : K ≃ₐ[E] K) = AlgEquiv.restrictScalars E (τ : K ≃ₐ[F'] K) ∧ ρ' σ = 1)
    (he' : ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal.ramificationIdx' (wK.under (𝓞 F')).asIdeal = 1)
    (hdvd' : Nat.card ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))))

    (q : ℕ) [Fact q.Prime] (L2 : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L2]
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K wK) L2] [FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K wK) L2]
    [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ]
    (Φ2 : wK.adicCompletion K ≃+* L2)
    (hΦ21 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L2 y = algebraMap ℚ_[q] L2 y)
    (hΦ22 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : (↥L2)ˣ), ((g • y : (↥L2)ˣ) : L2) = g • (y : L2))
    (hΦ23 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : wK.adicCompletion K), Φ2 (g • y) = g • Φ2 y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hbase2 : ExtCitation.LocalLevel.IsBase q L2 ↥(NumberField.PlaceDecomp.decomp E K wK) K₀)
    (u2 : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ))
    (hu2 : ExtCitation.LocalLevel.IsLocalFundamentalClass q L2 ↥(NumberField.PlaceDecomp.decomp E K wK) K₀ u2)

    (𝔣K : Ideal (𝓞 E)) (hadmK : NumberField.NormIndex.IsAdmissibleModulusOfDegree E K (Module.finrank E K) 𝔣K)
    (rK : (AdeleRing (𝓞 E) E)ˣ →* (K ≃ₐ[E] K))
    (hrK₁ : principalIdeles (𝓞 E) E ≤ rK.ker)
    (hrK₂ : rK.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E K).idelicNorm.range)
    (hrK₃ : Function.Surjective rK)
    (hrK₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣K u 1 →
      rK u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E K v ^ placeOrd E (projFin E u) v)

    (ιv : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ)
    (hιv : ∀ z, ιv z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hιv' : ∀ z, finPart v (ιv z) = z)
    (fE : (v.adicCompletion E)ˣ →* ↥(NumberField.PlaceDecomp.decomp E K wK))
    (hfE : ∀ z, ((fE z : ↥(NumberField.PlaceDecomp.decomp E K wK)) : K ≃ₐ[E] K) = rK (ιv z))

    (t : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) (ht : ∀ c, c ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (a : (v.adicCompletion E)ˣ) (b2 : (↥L2)ˣ)
    (hb2 : ((b2 : ↥L2) : PadicAlgCl q) =
      ((Φ2 (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E K (⟨wK, hv⟩ : v.Extension (𝓞 K))
        (a : v.adicCompletion E)) : ↥L2) : PadicAlgCl q))
    (hb2inv : (Additive.ofMul b2 : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).ρ.comp (ρ.ker).subtype))
    (hca : carryFun t ht htfin (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))
        ⟨Additive.ofMul b2, hb2inv⟩ ∈
      cocycles₂ ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))) :
    ∃ m : ℕ, (QuotientGroup.mk (fE a) : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) = t ^ m ∧
      ((infNatTrans ℤ (ρ.ker) 2).app (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))).hom
            ⟨carryFun t ht htfin (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))
              ⟨Additive.ofMul b2, hb2inv⟩, hca⟩) =
        (m * Nat.card (ρ.ker)) • u2 := by
  subst hv

  haveI : wK.asIdeal.IsPrime := wK.isPrime
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (K ≃ₐ[E] K) wK.asIdeal
  have hφd : φ ∈ NumberField.PlaceDecomp.decomp E K wK := M4aHerbrand.ArtInv.stabilizer_le_decomp' E K wK hφ.mem_stabilizer
  have hφ' := M4aHerbrand.ArtInv.isArithFrobAt_restrictNormal E F' K wK φ hφ
  obtain ⟨hmem', hgenF'⟩ := M4aHerbrand.ArtInv.zpowers_eq_decomp_of_isArithFrobAt_of_ramificationIdx_eq_one E F' (wK.under (𝓞 F')) he'
    (φ.restrictNormal F') hφ'
  have hρ'φ : ρ' ⟨φ, hφd⟩ = ⟨φ.restrictNormal F', hmem'⟩ := Subtype.ext (hρ'res ⟨φ, hφd⟩)
  have hgen' : ∀ d : ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))), d ∈ Subgroup.zpowers (ρ' ⟨φ, hφd⟩) :=
    fun d => hρ'φ ▸ hgenF' d
  have hexp' := M4aHerbrand.ArtInv.pow_natCard_decomp_eq_one_of_adjoin E F F' K hgen wK ρ hρres ρ' hρ'res hdvd'
  exact D45 E F' K (wK.under (𝓞 E)) wK rfl he' ρ' hρ'surj hρ'ker hρ'lift φ hφd hφ hgen' hexp' q L2 Φ2 hΦ21 hΦ22 hΦ23
    K₀ hbase2 u2 hu2 𝔣K hadmK rK hrK₁ hrK₂ hrK₃ hrK₄ ιv hιv hιv' fE hfE (ρ.ker) t ht htfin a b2 hb2 hb2inv hca

end S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer
end P2MW
export P2MW.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer (solution)
