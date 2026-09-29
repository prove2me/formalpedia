-- Prove2me | solution 1 for M4aHerbrand.exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6fc4ae19-3294-5a26-92f0-6c729d388622

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_CyclicCarry
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap
import Theorems.Thm_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
p2m_open "CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp Pointwise

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply principalIdeles IdeleGaloisDescent exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap exists_hom_res_decomp_ideles_adicCompletion_apply idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
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

end M4aHerbrand.ArtInv
namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply principalIdeles IdeleGaloisDescent exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap exists_hom_res_decomp_ideles_adicCompletion_apply idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
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
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply principalIdeles IdeleGaloisDescent exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap exists_hom_res_decomp_ideles_adicCompletion_apply idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
namespace LocalSum
p2m_open "M4aHerbrand"

theorem addCircle_div_eq_div_of_dvd {N : ℕ} (hN : 0 < N) {a b : ℤ} (h : (N : ℤ) ∣ a - b) :
    ((((a : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) = ((((b : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) := by
  obtain ⟨k, hk⟩ := h
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨k, ?_⟩
  rw [zsmul_one, ← sub_div, eq_div_iff hN']
  have hk' : ((a : ℚ) - (b : ℚ)) = ((N : ℤ) : ℚ) * (k : ℚ) := by exact_mod_cast hk
  rw [hk']
  push_cast
  ring

theorem exists_addMonoidHom_addCircle {M : Type*} [AddCommGroup M] (g : M) (N : ℕ) (hN : 0 < N)
    (hgen : ∀ c : M, ∃ m : ℤ, c = m • g) (hord : ∀ m : ℤ, m • g = 0 → (N : ℤ) ∣ m) :
    ∃ ι : M →+ AddCircle (1 : ℚ), ∀ (c : M) (m : ℤ), c = m • g →
      ι c = ((((m : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) := by
  classical

  have hwd : ∀ (c : M) (m m' : ℤ), c = m • g → c = m' • g → (N : ℤ) ∣ m - m' := by
    intro c m m' h h'
    apply hord
    rw [sub_zsmul, ← h, ← h']
    exact add_neg_cancel c
  let f : M → AddCircle (1 : ℚ) := fun c => (((((Classical.choose (hgen c) : ℤ) : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ))
  have hf : ∀ (c : M) (m : ℤ), c = m • g → f c = ((((m : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) := fun c m h =>
    addCircle_div_eq_div_of_dvd hN (hwd c _ _ (Classical.choose_spec (hgen c)) h)
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, fun c m h => hf c m h⟩
  · rw [hf 0 0 (by rw [zero_zsmul])]
    simp
  · intro c d
    obtain ⟨m, hm⟩ := hgen c
    obtain ⟨m', hm'⟩ := hgen d
    show f (c + d) = f c + f d
    rw [hf c m hm, hf d m' hm', hf (c + d) (m + m') (by rw [hm, hm', add_zsmul]), ← AddCircle.coe_add]
    push_cast
    rw [add_div]

section Cohomology

variable {G : Type} [Group G]

theorem map_top_subtype_injective (B : Rep ℤ G) :
    Function.Injective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom := by
  let eT : G →* ↥(⊤ : Subgroup G) := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).symm.toMonoidHom
  have key : groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2 ≫
      groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype B))) 2 = 𝟙 _ := by
    rw [← groupCohomology.map_comp]
    exact groupCohomology.map_id (B := B) (n := 2)
  have hleft : ∀ y : groupCohomology B 2,
      (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype B))) 2).hom
        ((groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom y) = y := by
    intro y
    have hy := congrArg (fun T => (ModuleCat.Hom.hom T) y) key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
    exact hy
  exact Function.LeftInverse.injective hleft

variable {A B : Rep ℤ G} (θ : B ⟶ A) (θ' : A ⟶ B) (u : groupCohomology B 2)

theorem exists_eq_zsmul_map_of_span (hθ'θ : θ' ≫ θ = 𝟙 A)
    (hspan : Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} = ⊤)
    (c : groupCohomology A 2) :
    ∃ m : ℤ, c = m • (groupCohomology.map (MonoidHom.id G) θ 2).hom u := by
  have hback : ∀ y : groupCohomology A 2,
      (groupCohomology.map (MonoidHom.id G) θ 2).hom ((groupCohomology.map (MonoidHom.id G) θ' 2).hom y) = y := by
    intro y
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ' θ 2)
    simp only [hθ'θ, groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  set X' := (groupCohomology.map (MonoidHom.id G) θ' 2).hom c with hX'
  have hmem : (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom X' ∈
      Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} := by
    rw [hspan]; trivial
  obtain ⟨m₀, hm₀⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨m₀, ?_⟩
  have hXu : X' = m₀ • u := by
    apply map_top_subtype_injective B
    rw [map_zsmul, ← hm₀]
    exact int_smul_eq_zsmul _ m₀ _
  calc c = (groupCohomology.map (MonoidHom.id G) θ 2).hom X' := (hback _).symm
    _ = m₀ • (groupCohomology.map (MonoidHom.id G) θ 2).hom u := by rw [hXu, map_zsmul]

theorem natCard_dvd_of_zsmul_map_eq_zero [Finite G] (hθθ' : θ ≫ θ' = 𝟙 B)
    (hcard : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype B) 2) = Fintype.card S)
    (hspan : Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} = ⊤)
    (m : ℤ) (hm : m • (groupCohomology.map (MonoidHom.id G) θ 2).hom u = 0) : (Nat.card G : ℤ) ∣ m := by

  have hleft : ∀ y : groupCohomology B 2,
      (groupCohomology.map (MonoidHom.id G) θ' 2).hom ((groupCohomology.map (MonoidHom.id G) θ 2).hom y) = y := by
    intro y
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ θ' 2)
    simp only [hθθ', groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  have hm' : m • u = 0 := by
    have h := congrArg ((groupCohomology.map (MonoidHom.id G) θ' 2).hom) hm
    rw [map_zsmul, map_zero, hleft] at h
    exact h

  haveI : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  have hc := hcard ⊤
  haveI : Finite ↥(groupCohomology (Rep.res (⊤ : Subgroup G).subtype B) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
  haveI : Fintype ↥(groupCohomology (Rep.res (⊤ : Subgroup G).subtype B) 2) := Fintype.ofFinite _
  set u₀ := (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u with hu₀
  have hgen : ∀ y, y ∈ AddSubgroup.zmultiples u₀ := fun y => by
    have hy : y ∈ Submodule.span ℤ {u₀} := by rw [hspan]; trivial
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨k, (int_smul_eq_zsmul _ k u₀).symm.trans hk⟩
  have hordu : addOrderOf u₀ = Nat.card G := by
    rw [addOrderOf_eq_card_of_forall_mem_zmultiples hgen, hc, ← Nat.card_eq_fintype_card, Subgroup.card_top]
  have hm0 : m • u₀ = 0 := by
    rw [hu₀, ← map_zsmul, hm', map_zero]
  rw [← hordu]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hm0

end Cohomology

end M4aHerbrand.LocalSum

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply principalIdeles IdeleGaloisDescent exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap exists_hom_res_decomp_ideles_adicCompletion_apply idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
namespace LocalSum
p2m_open "M4aHerbrand"

section Bridge

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  (w : HeightOneSpectrum (𝓞 F))

theorem exists_unitsTransport {q : ℕ} [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ]
    (Φ : (w.adicCompletion F) ≃+* L)
    (hΦ₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (hΦ₃ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (w.adicCompletion F)), Φ (g • y) = g • Φ y) :
    ∃ (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ)
      (θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ),
      (∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = Φ.symm (y : L)) ∧
      θ ≫ θ' = 𝟙 _ ∧ θ' ≫ θ = 𝟙 _ := by
  let ΨM : (↥L)ˣ →* (w.adicCompletion F)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΨM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ΨM (g • y) = g • ΨM y := by
    intro g y
    apply Units.ext
    show Φ.symm ((g • y : (↥L)ˣ) : ↥L) = ((g • ΨM y : (w.adicCompletion F)ˣ) : (w.adicCompletion F))
    rw [hΦ₂ g y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ.injective
    rw [hΦ₃ g, RingEquiv.apply_symm_apply]
    congr 1
    exact (Φ.apply_symm_apply _).symm
  let ΦM : (w.adicCompletion F)ˣ →* (↥L)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (m : (w.adicCompletion F)ˣ), ΦM (g • m) = g • ΦM m := by
    intro g m
    apply Units.ext
    rw [hΦ₂ g (ΦM m)]
    show Φ ((g • m : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = g • Φ (m : (w.adicCompletion F))
    rw [NumberField.PlaceDecomp.coe_smul_units, hΦ₃ g]
  refine ⟨M4aHerbrand.repHomOfMulEquivariant ΨM hΨM, M4aHerbrand.repHomOfMulEquivariant ΦM hΦM, fun y => rfl, ?_, ?_⟩
  · refine Rep.hom_ext ?_
    ext z
    rw [Rep.hom_comp, Rep.hom_id]
    show (M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom ((M4aHerbrand.repHomOfMulEquivariant ΨM hΨM).hom z) = z
    rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply, M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
    apply Units.ext
    exact Φ.apply_symm_apply _
  · refine Rep.hom_ext ?_
    ext z
    rw [Rep.hom_comp, Rep.hom_id]
    show (M4aHerbrand.repHomOfMulEquivariant ΨM hΨM).hom ((M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom z) = z
    rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply, M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
    apply Units.ext
    exact Φ.symm_apply_apply _

structure BridgeDatum where
  q : ℕ
  [hq : Fact q.Prime]
  L : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd : FiniteDimensional ℚ_[q] L]
  [sma : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L]
  [fs : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) L]
  [mda : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ]
  Φ : (w.adicCompletion F) ≃+* L
  h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x
  h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L)
  h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (w.adicCompletion F)), Φ (g • y) = g • Φ y
  hqw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal
  K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd₀ : FiniteDimensional ℚ_[q] K₀]
  base : ExtCitation.LocalLevel.IsBase q L ↥(NumberField.PlaceDecomp.decomp E F w) K₀
  θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ
  θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ
  hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = Φ.symm (y : L)
  hθθ' : θ ≫ θ' = 𝟙 _
  hθ'θ : θ' ≫ θ = 𝟙 _
  u : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ)
  hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E F w) K₀ u
  hcard : ∀ (S : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w)) [Fintype S],
    Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ)) 2) = Fintype.card S
  hspan : ∀ S : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w),
    Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ))) 2).hom u} = ⊤

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

theorem nonempty_bridgeDatum [IsCyclic (F ≃ₐ[E] F)] : Nonempty (BridgeDatum E F w) := by
  obtain ⟨q, hq, L, fd, sma, fs, mda, Φ, h1, h2, h3, hqw⟩ := NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion E F w
  obtain ⟨K₀, fd₀, base⟩ := exists_isBase q L ↥(NumberField.PlaceDecomp.decomp E F w) h1
  obtain ⟨θ, θ', hθ, hθθ', hθ'θ⟩ := exists_unitsTransport E F w L Φ h2 h3
  have hcomm : ∀ a b : F ≃ₐ[E] F, a * b = b * a := fun a b => by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
    obtain ⟨i, rfl⟩ := hg a
    obtain ⟨j, rfl⟩ := hg b
    rw [← zpow_add, ← zpow_add, add_comm]
  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F w) :=
    Group.isSolvable_of_comm (fun g₁ g₂ => Subtype.ext (hcomm (g₁ : F ≃ₐ[E] F) (g₂ : F ≃ₐ[E] F)))
  obtain ⟨u, hu⟩ := (ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E F w) h1 h2 hsolv K₀ base).exists
  obtain ⟨-, hcard, hspan⟩ :=
    ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E F w) h1 h2 hsolv K₀ base u hu
  exact ⟨⟨q, L, Φ, h1, h2, h3, hqw, K₀, base, θ, θ', hθ, hθθ', hθ'θ, u, hu, hcard, hspan⟩⟩

end Bridge

section Chosen

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)]
  (w : HeightOneSpectrum (𝓞 F))

noncomputable def bd : BridgeDatum E F w := Classical.choice (nonempty_bridgeDatum E F w)

noncomputable def gen : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2 :=
  (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (bd E F w).θ 2).hom (bd E F w).u

theorem gen_generates (c : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2) :
    ∃ m : ℤ, c = m • gen E F w :=
  exists_eq_zsmul_map_of_span (bd E F w).θ (bd E F w).θ' (bd E F w).u (bd E F w).hθ'θ ((bd E F w).hspan ⊤) c

theorem gen_order (m : ℤ) (hm : m • gen E F w = 0) : (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℤ) ∣ m :=
  natCard_dvd_of_zsmul_map_eq_zero (bd E F w).θ (bd E F w).θ' (bd E F w).u (bd E F w).hθθ'
    (fun S => (bd E F w).hcard S) ((bd E F w).hspan ⊤) m hm

theorem exists_iota : ∃ ι : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2 →+ AddCircle (1 : ℚ),
    ∀ (c : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2) (m : ℤ), c = m • gen E F w →
      ι c = ((((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ)) : AddCircle (1 : ℚ)) :=
  exists_addMonoidHom_addCircle (gen E F w) (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)) Nat.card_pos (gen_generates E F w) (gen_order E F w)

noncomputable def iota : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2 →+ AddCircle (1 : ℚ) :=
  Classical.choose (exists_iota E F w)

theorem iota_spec (c : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2) (m : ℤ) (h : c = m • gen E F w) :
    iota E F w c = ((((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ)) : AddCircle (1 : ℚ)) :=
  Classical.choose_spec (exists_iota E F w) c m h

end Chosen

end M4aHerbrand.LocalSum

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply principalIdeles IdeleGaloisDescent exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap exists_hom_res_decomp_ideles_adicCompletion_apply idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
namespace LocalGen
p2m_open "M4aHerbrand"

theorem exists_global_mul_pow (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 0 < n)
    (hpow : ∃ m : ℕ, ∀ a : v.adicCompletion E, Valued.v (a - 1) ≤ WithZero.exp (-(m : ℤ)) → ∃ c : v.adicCompletion E, c ^ n = a)
    (a₀ : (v.adicCompletion E)ˣ) :
    ∃ (a : Eˣ) (c : (v.adicCompletion E)ˣ), Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a = a₀ * c ^ n := by
  obtain ⟨m, hm⟩ := hpow
  set γ₀ : WithZero (Multiplicative ℤ) := Valued.v (a₀ : v.adicCompletion E) with hγ₀def
  have hγ₀ : γ₀ ≠ 0 := (Valuation.ne_zero_iff _).2 a₀.ne_zero

  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer E
  set d₀ : v.adicCompletion E := (algebraMap E (v.adicCompletion E) π) ^ m * (a₀ : v.adicCompletion E) with hd₀
  have hvd₀ : Valued.v d₀ = WithZero.exp (-(m : ℤ)) * γ₀ := by
    rw [hd₀, Valuation.map_mul, Valuation.map_pow]
    congr 1
    rw [show (algebraMap E (v.adicCompletion E) π) = ((π : E) : v.adicCompletion E) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hd₀0 : Valued.v d₀ ≠ 0 := by rw [hvd₀]; exact mul_ne_zero WithZero.exp_ne_zero hγ₀

  have hnhds : {y : v.adicCompletion E | Valued.v (y - (a₀ : v.adicCompletion E)) < Valued.v d₀} ∈ nhds (a₀ : v.adicCompletion E) := by
    rw [Valued.mem_nhds]
    have hd₀ne : d₀ ≠ 0 := (Valuation.ne_zero_iff Valued.v).1 hd₀0
    exact ⟨Units.mk0 (Valued.v.restrict d₀) ((Valuation.ne_zero_iff _).2 hd₀ne), fun y hy => (Valuation.restrict_lt_iff (v := Valued.v)).1 hy⟩
  obtain ⟨y, ⟨e, rfl⟩, hy⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := E) v).inter_nhds_nonempty hnhds
  simp only [Set.mem_setOf_eq, hvd₀] at hy

  have hy0 : algebraMap E (v.adicCompletion E) e ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg] at hy
    have h1 : WithZero.exp (-(m : ℤ)) * γ₀ ≤ 1 * γ₀ := by
      apply mul_le_mul_left
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by omega)
    rw [one_mul] at h1
    exact (lt_irrefl γ₀) (lt_of_lt_of_le hy h1)
  have he0 : e ≠ 0 := fun h => hy0 (by rw [h, map_zero])

  set q : v.adicCompletion E := algebraMap E (v.adicCompletion E) e * ((a₀⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) with hq
  have hq1 : Valued.v (q - 1) ≤ WithZero.exp (-(m : ℤ)) := by
    have hqe : q - 1 = (algebraMap E (v.adicCompletion E) e - (a₀ : v.adicCompletion E)) * ((a₀⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
      rw [hq, sub_mul, Units.mul_inv]
    rw [hqe, Valuation.map_mul, map_units_inv]
    have hle : Valued.v (algebraMap E (v.adicCompletion E) e - (a₀ : v.adicCompletion E)) * γ₀⁻¹ ≤ WithZero.exp (-(m : ℤ)) * γ₀ * γ₀⁻¹ :=
      mul_le_mul_left hy.le _
    rwa [mul_assoc, mul_inv_cancel₀ hγ₀, mul_one] at hle
  obtain ⟨c, hc⟩ := hm q hq1
  have hq0 : q ≠ 0 := mul_ne_zero hy0 (Units.ne_zero _)
  have hc0 : c ≠ 0 := by
    intro h
    apply hq0
    rw [← hc, h, zero_pow hn.ne']
  refine ⟨Units.mk0 e he0, Units.mk0 c hc0, Units.ext ?_⟩
  show algebraMap E (v.adicCompletion E) e = (a₀ : v.adicCompletion E) * c ^ n
  rw [hc, hq, mul_comm, mul_assoc, Units.inv_mul, mul_one]

end M4aHerbrand.LocalGen

open M4aHerbrand.ArtInv M4aHerbrand.LocalSum M4aHerbrand.LocalGen in
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
    ∃ (a : Eˣ) (x : (AdeleRing (𝓞 E) E)ˣ),
      x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) ∧
      finPart v x = Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a ∧
      r x ∈ NumberField.PlaceDecomp.decomp E F w ∧
      ∀ g : ↥(NumberField.PlaceDecomp.decomp E F w), (g : F ≃ₐ[E] F) ∈ Subgroup.zpowers (r x) := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance

  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
  have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s
  obtain ⟨k, hkD, hkgen, hkcard⟩ := exists_pow_index_generates s hs (NumberField.PlaceDecomp.decomp E F w)
  set t : ↥(NumberField.PlaceDecomp.decomp E F w) := ⟨s ^ k, hkD⟩ with ht
  have htfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  have hdpos : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := Nat.card_pos

  obtain ⟨Ψ, hΨ, hΨsurj, -, hΨcard⟩ :=
    NumberField.PlaceDecomp.exists_carryClassHom_surjective_ker_eq_norms_adicCompletion E F v w hw t hkgen htfin

  obtain ⟨a₀, ha₀⟩ := hΨsurj (Multiplicative.ofAdd (gen E F w))
  obtain ⟨a, c, hac⟩ := exists_global_mul_pow E v (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)) hdpos
    (IsDedekindDomain.HeightOneSpectrum.exists_forall_exists_pow_eq_of_valued_sub_one_le E v (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)) hdpos) a₀
  set aE : (v.adicCompletion E)ˣ := Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a with haE
  have hΨa : Ψ aE = Multiplicative.ofAdd (gen E F w) := by
    rw [hac, map_mul, map_pow, ha₀]
    have hone : Ψ c ^ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) = 1 := by
      rw [← hΨcard, Nat.card_congr (Multiplicative.ofAdd (α := groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)))]
      exact pow_card_eq_one'
    rw [hone, mul_one]

  refine ⟨a, singleIdele E v aE, singleIdele_mem_idelesTrivialOn aE, finPart_singleIdele_self aE,
    idelicArtinMap_mem_decomp E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v aE _ (singleIdele_mem_idelesTrivialOn aE) (finPart_singleIdele_self aE) w hw, ?_⟩
  set x := singleIdele E v aE with hxdef
  have hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) := singleIdele_mem_idelesTrivialOn aE
  have hxv : finPart v x = aE := finPart_singleIdele_self aE

  let D : IdeleGaloisDescent (𝓞 F) E F := genuineDescentDatum E F
  letI instI : MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ := MulDistribMulAction.compHom _ D.unitsAct
  have hactI : ∀ (g : (F ≃ₐ[E] F)) (y : (AdeleRing (𝓞 F) F)ˣ), g • y = D.unitsAct g y := fun _ _ => rfl
  letI instF : MulDistribMulAction (F ≃ₐ[E] F) Fˣ := Units.mulDistribMulActionRight
  have hactF : ∀ (g : (F ≃ₐ[E] F)) (b : Fˣ), ((g • b : Fˣ) : F) = g (b : F) := fun _ _ => rfl
  let jM : Fˣ →* (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)
  have hjM : ∀ (g : F ≃ₐ[E] F) (b : Fˣ), jM (g • b) = g • jM b := by
    intro g b
    apply Units.ext
    show algebraMap F (AdeleRing (𝓞 F) F) ((g • b : Fˣ) : F) = ((D.unitsAct g (jM b) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    rw [hactF]
    show _ = D.act g (algebraMap F (AdeleRing (𝓞 F) F) (b : F))
    rw [D.compat]
  let j : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ :=
    M4aHerbrand.repHomOfMulEquivariant jM hjM
  have hj : ∀ b : Fˣ, j.hom (Additive.ofMul b) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) b) :=
    fun b => rfl
  obtain ⟨prG, hprG⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E F D hactI

  have haF : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ).ρ s (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) =
      Additive.ofMul (Units.map (algebraMap E F : E →* F) a) := by
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
    change Additive.ofMul (s • Units.map (algebraMap E F : E →* F) a) = _
    congr 1
    apply Units.ext
    rw [hactF]
    exact AlgEquiv.commutes s (a : E)
  have hc := groupCohomology.carryFun_mem_cocycles2 (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin
    (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) haF

  haveI := (bd E F w).hq
  haveI := (bd E F w).fd
  letI := (bd E F w).sma
  haveI := (bd E F w).fs
  letI := (bd E F w).mda
  haveI := (bd E F w).fd₀

  obtain ⟨nw, i, h1, h2, h3⟩ :=
    M4aHerbrand.exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap E F s hs hfin D hactI hactF j hj
      v w hw (prG w) (hprG w) 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ a x hx hxv hc
      (bd E F w).q (bd E F w).L (bd E F w).Φ (bd E F w).h1 (bd E F w).h2 (bd E F w).h3 (bd E F w).K₀ (bd E F w).base
      (bd E F w).θ (bd E F w).hθ (bd E F w).u (bd E F w).hu

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
  have coreII : (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (prG w) 2).hom
          ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom
            ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom
              ⟨carryFun (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩)) =
      (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩ := by
    have hcomp := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) (MonoidHom.id (F ≃ₐ[E] F)) (NumberField.PlaceDecomp.decomp E F w).subtype j (prG w) 2
    have happ := congrArg (fun T => (ModuleCat.Hom.hom T) ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom
      ⟨carryFun (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩)) hcomp
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
    rw [← happ]
    have hφa : ((Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map j ≫ prG w).hom
        (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) = Additive.ofMul aw := by
      rw [Rep.hom_comp]
      show (prG w).hom (j.hom (Additive.ofMul (Units.map (algebraMap E F : E →* F) a))) = Additive.ofMul aw
      rw [hj]
      erw [hprG]
      congr 1
    have hzb : carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin
        (((Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map j ≫ prG w).hom (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)))
        ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) := by
      rw [hφa]; exact hcw
    have key := groupCohomology.map_carry_H2pi_eq_smul_carry ((MonoidHom.id (F ≃ₐ[E] F)).comp (NumberField.PlaceDecomp.decomp E F w).subtype)
      (NumberField.PlaceDecomp.decomp E F w).subtype_injective s hs hfin k t rfl hkgen htfin
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
      ((Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map j ≫ prG w)
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

  have haw : Units.map (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
      v.adicCompletion E →* w.adicCompletion F) aE = aw := by
    apply Units.ext
    show IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) (algebraMap E (v.adicCompletion E) (a : E)) =
      algebraMap F (w.adicCompletion F) (algebraMap E F (a : E))
    rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, map_one, ← Algebra.algebraMap_eq_smul_one]
  have hΨval : Ψ aE = Multiplicative.ofAdd ((H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩) := by
    have hc' : carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul (Units.map
        (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
          v.adicCompletion E →* w.adicCompletion F) aE)) ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) := by
      rw [haw]; exact hcw
    rw [hΨ aE hc']
    congr 2
    exact Subtype.ext (congrArg (fun z => carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul z)) haw)

  have hL : (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩ = nw • gen E F w := by
    rw [← coreII, h1]
    rfl
  have hgen : gen E F w = nw • gen E F w :=
    (Multiplicative.ofAdd.injective (hΨa.symm.trans hΨval)).trans hL
  have hdvd : (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℤ) ∣ nw - 1 :=
    gen_order E F w (nw - 1) (by rw [sub_zsmul, one_zsmul, ← hgen]; abel)

  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hkcard
    exact (Nat.card_pos (α := F ≃ₐ[E] F)).ne' hkcard.symm
  have hz : ∃ z : ℤ, (i : ℤ) = nw * k + z * (Nat.card (F ≃ₐ[E] F)) := by
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h3
    obtain ⟨z, hz⟩ := h3
    refine ⟨-z, ?_⟩
    rw [zsmul_one] at hz
    have hDq : (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    have hcardq : (Nat.card (F ≃ₐ[E] F) : ℚ) = (k : ℚ) * (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) := by exact_mod_cast hkcard.symm
    rw [hcardq] at hz
    have hz2 : (z : ℚ) * ((k : ℚ) * (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ)) = (nw : ℚ) * k - (i : ℚ) := by
      rw [hz]
      field_simp
    have hq : ((i : ℤ) : ℚ) = (((nw * k + (-z) * (Nat.card (F ≃ₐ[E] F) : ℕ)) : ℤ) : ℚ) := by
      push_cast
      rw [hcardq]
      linarith
    exact_mod_cast hq
  obtain ⟨z, hz⟩ := hz
  have hsD : (s ^ k) ^ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) = 1 := by
    have h0 : t ^ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) = 1 := pow_card_eq_one'
    have h0' := congrArg (fun g : ↥(NumberField.PlaceDecomp.decomp E F w) => (g : F ≃ₐ[E] F)) h0
    simpa [ht] using h0'
  have hrx : r x = s ^ k := by
    rw [h2, ← zpow_natCast s i, hz, zpow_add, zpow_mul', zpow_mul]
    simp only [zpow_natCast, pow_card_eq_one', mul_one]
    obtain ⟨q', hq'⟩ := hdvd
    have hnw : nw = 1 + (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℤ) * q' := by linarith
    rw [hnw, zpow_add, zpow_one, zpow_mul, zpow_natCast, hsD, one_zpow, mul_one]

  intro g
  rw [hrx]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hkgen g)
  refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
  rw [← hm, Subgroup.coe_zpow]

end S_M4aHerbrand_exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic
end P2MW
export P2MW.S_M4aHerbrand_exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic (solution)
