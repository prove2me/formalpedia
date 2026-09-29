-- Prove2me | solution 1 for M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6084404d-cd06-5f6b-8e4b-cf7f4ea413e4

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_NumberField_PlaceAbove
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower
import Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker
import Theorems.Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup
import Theorems.Thm_M4aHerbrand_exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup
import Theorems.Thm_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "instance" "instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"
p2m_attr_erase "simp" "groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ exists_fundamentalClass_ideleClassGroup exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp"
namespace DescAlg
p2m_open "M4aHerbrand"

theorem zsmul_eq_zero_iff_dvd_of_span_eq_top {M : Type*} [AddCommGroup M] (g : M) (n : ℕ) (hn : n ≠ 0)
    (hcard : Nat.card M = n) (hspan : Submodule.span ℤ {g} = ⊤) :
    ∀ k : ℤ, k • g = 0 ↔ (n : ℤ) ∣ k := by
  have hz : AddSubgroup.zmultiples g = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℤ {g} := hspan ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact AddSubgroup.zsmul_mem_zmultiples g a
  have hord : addOrderOf g = n := by
    rw [← Nat.card_zmultiples, hz, AddSubgroup.card_top, hcard]
  intro k
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hord]

theorem isCoprime_of_eq_zsmul {M : Type*} [AddCommGroup M] (v w : M) (n : ℕ) (hn : n ≠ 0)
    (hv : ∀ k : ℤ, k • v = 0 ↔ (n : ℤ) ∣ k) (hw : (n : ℤ) • w = 0) (a : ℤ) (hvw : v = a • w) :
    IsCoprime a n := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set c : ℕ := Int.gcd a n with hc
  have hcn : (c : ℤ) ∣ (n : ℤ) := Int.gcd_dvd_right ..
  have hca : (c : ℤ) ∣ a := Int.gcd_dvd_left ..
  obtain ⟨n₁, hn₁⟩ := hcn
  obtain ⟨a₁, ha₁⟩ := hca
  have hc0 : (c : ℤ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn₁
    exact hn (by exact_mod_cast hn₁)

  have h1 : n₁ • v = 0 := by
    rw [hvw, smul_smul]
    have : n₁ * a = a₁ * (n : ℤ) := by rw [ha₁, hn₁]; ring
    rw [this, ← smul_smul, hw, smul_zero]
  have h2 : (n : ℤ) ∣ n₁ := (hv n₁).1 h1

  have hn₁0 : n₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hn₁
    exact hn (by exact_mod_cast hn₁)
  rw [hn₁] at h2
  obtain ⟨t, ht⟩ := h2
  have : (c : ℤ) * t = 1 := by
    have h' : n₁ * ((c : ℤ) * t) = n₁ * 1 := by rw [mul_one]; linarith [ht]
    exact mul_left_cancel₀ hn₁0 h'
  have hc1 : (c : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) this
  exact_mod_cast hc1

theorem exists_isCoprime_map_zsmul_eq_nsmul {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (f : M →+ M') (hf : Function.Injective f) (n N : ℕ) (hn : n ≠ 0) (hN : N ≠ 0)
    (g : M) (hg : ∀ k : ℤ, k • g = 0 ↔ (n : ℤ) ∣ k)
    (g' : M') (hg'span : Submodule.span ℤ {g'} = ⊤) (hg' : ∀ k : ℤ, k • g' = 0 ↔ ((n * N : ℕ) : ℤ) ∣ k)
    (u' : M') (hu' : ∀ k : ℤ, k • u' = 0 ↔ ((n * N : ℕ) : ℤ) ∣ k) :
    ∃ d : ℤ, IsCoprime d n ∧ f (d • g) = (N : ℤ) • u' := by

  have hv : ∀ k : ℤ, k • f g = 0 ↔ (n : ℤ) ∣ k := fun k => by
    rw [← map_zsmul, ← hg k]
    exact ⟨fun h => hf (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.1 (show f g ∈ Submodule.span ℤ {g'} from hg'span ▸ Submodule.mem_top)
  have hNa' : (N : ℤ) ∣ a' := by
    have h1 : ((n : ℤ) * a') • g' = 0 := by rw [← smul_smul, ha', (hv n).2 dvd_rfl]
    have h2 := (hg' _).1 h1
    push_cast at h2
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hn : (n : ℤ) ≠ 0)).1 h2
  obtain ⟨a, rfl⟩ := hNa'

  have hw : (n : ℤ) • ((N : ℤ) • g') = 0 := by
    rw [smul_smul]
    exact (hg' _).2 (by push_cast; exact dvd_rfl)
  have hvw : f g = a • ((N : ℤ) • g') := by rw [smul_smul, mul_comm, ha']
  have ha : IsCoprime a n := isCoprime_of_eq_zsmul (f g) _ n hn hv hw a hvw

  obtain ⟨e', he'⟩ := Submodule.mem_span_singleton.1 (show u' ∈ Submodule.span ℤ {g'} from hg'span ▸ Submodule.mem_top)
  have he : IsCoprime e' n := by
    have h := isCoprime_of_eq_zsmul u' g' (n * N) (Nat.mul_ne_zero hn hN) hu' ((hg' _).2 dvd_rfl) e' he'.symm
    rw [Nat.cast_mul] at h
    exact h.of_mul_right_left

  obtain ⟨x, y, hxy⟩ := ha
  refine ⟨e' * x, he.mul_left ⟨a, y, by linarith [hxy]⟩, ?_⟩
  rw [map_zsmul, hvw, smul_smul, ← he']
  have hre : e' * x * a = e' + (-(e' * y)) * (n : ℤ) := by linear_combination e' * hxy
  rw [hre, add_smul, ← smul_smul (-(e' * y)), hw, smul_zero, add_zero, smul_comm]

theorem span_singleton_zsmul_eq_top {M : Type*} [AddCommGroup M] (x : M) (s n : ℕ) (hs : s ≠ 0)
    (hcard : Nat.card M = s) (hsn : s ∣ n) (hspan : Submodule.span ℤ {x} = ⊤) (d : ℤ) (hd : IsCoprime d n) :
    Submodule.span ℤ {d • x} = ⊤ := by
  have hds : IsCoprime d s := hd.of_isCoprime_of_dvd_right (by exact_mod_cast hsn)
  obtain ⟨d', y, hd'y⟩ := hds
  have hsx : (s : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (hcard ▸ addOrderOf_dvd_natCard x)
  have hx : x = d' • (d • x) := by
    calc x = (1 : ℤ) • x := (one_zsmul x).symm
      _ = (d' * d + y * s) • x := by rw [hd'y]
      _ = d' • (d • x) + y • ((s : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
      _ = d' • (d • x) := by rw [hsx, smul_zero, add_zero]
  rw [eq_top_iff, ← hspan, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.2 ⟨d', hx.symm⟩

theorem span_singleton_map_eq_top_of_mem {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (r : M →+ M')
    (u₀ u₁ : M) (h0 : Submodule.span ℤ {r u₀} = ⊤) (hmem : u₀ ∈ Submodule.span ℤ {u₁}) :
    Submodule.span ℤ {r u₁} = ⊤ := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hmem
  rw [eq_top_iff, ← h0, Submodule.span_singleton_le_iff_mem, map_zsmul]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)

theorem natCard_dvd_iff_of_span_eq_top {M : Type*} [AddCommGroup M] [Finite M] (g : M)
    (hspan : Submodule.span ℤ {g} = ⊤) (k : ℤ) : k • g = 0 ↔ (Nat.card M : ℤ) ∣ k :=
  zsmul_eq_zero_iff_dvd_of_span_eq_top g (Nat.card M) (Nat.card_pos.ne') rfl hspan k

end M4aHerbrand.DescAlg

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ exists_fundamentalClass_ideleClassGroup exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp"
namespace DescAlg
p2m_open "M4aHerbrand"

theorem exists_coprime_mul_pow_eq (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    ∃ m a : ℕ, p.Coprime m ∧ m * p ^ a = n := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  exact ⟨m, a, (Nat.Prime.coprime_iff_not_dvd hp).2 hm, by ring⟩

theorem coprime_mul_pow_inj (p : ℕ) (hp : p.Prime) {m m' a a' : ℕ} (hm : p.Coprime m) (hm' : p.Coprime m')
    (h : m * p ^ a = m' * p ^ a') : m = m' ∧ a = a' := by
  have hm0 : m ≠ 0 := by rintro rfl; simp [Nat.coprime_zero_right, hp.ne_one] at hm
  have hm0' : m' ≠ 0 := by rintro rfl; simp [Nat.coprime_zero_right, hp.ne_one] at hm'
  haveI := Fact.mk hp
  have ha : a = a' := by
    have h1 := congrArg (padicValNat p) h
    rw [padicValNat.mul hm0 (pow_ne_zero _ hp.ne_zero), padicValNat.mul hm0' (pow_ne_zero _ hp.ne_zero),
      padicValNat.prime_pow, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hm),
      padicValNat.eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hm')] at h1
    simpa using h1
  subst ha
  exact ⟨Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h, rfl⟩

theorem coprime_mul_and_mul_pow_add_eq (p : ℕ) {m a k₀ b D D' k : ℕ} (hm : p.Coprime m) (hk₀ : p.Coprime k₀)
    (hD : m * p ^ a = D) (hk : k₀ * p ^ b = k) (hD' : D' = k * D) :
    p.Coprime (m * k₀) ∧ (m * k₀) * p ^ (a + b) = D' := by
  refine ⟨Nat.Coprime.mul_right hm hk₀, ?_⟩
  rw [hD', ← hD, ← hk, pow_add]
  ring

theorem nsmul_eq_zero_of_mul_pow_nsmul_of_mul_coprime_nsmul {M : Type*} [AddCommGroup M] (x : M) (p m a t : ℕ)
    (hp : p.Prime) (ht : p.Coprime t) (h₁ : (m * p ^ a) • x = 0) (h₂ : (m * t) • x = 0) : m • x = 0 := by
  have hc : (p ^ a).Coprime t := Nat.Coprime.pow_left a ht

  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc)
  have h₁' : ((m : ℤ) * (p : ℤ) ^ a) • x = 0 := by exact_mod_cast h₁
  have h₂' : ((m : ℤ) * (t : ℤ)) • x = 0 := by exact_mod_cast h₂
  have : (m : ℤ) • x = 0 := by
    have e : (m : ℤ) = u * ((m : ℤ) * (p : ℤ) ^ a) + v * ((m : ℤ) * (t : ℤ)) := by
      have := huv
      push_cast at this ⊢
      linear_combination (-(m : ℤ)) * this
    rw [e, add_smul, mul_smul u, mul_smul v, h₁', h₂', smul_zero, smul_zero, add_zero]
  exact_mod_cast this

theorem nsmul_eq_zero_of_mul_pow_nsmul_of_mul_isCoprime_zsmul {M : Type*} [AddCommGroup M] (x : M) (p m a : ℕ) (t : ℤ)
    (hp : p.Prime) (ht : IsCoprime (p : ℤ) t) (h₁ : (m * p ^ a) • x = 0) (h₂ : ((m : ℤ) * t) • x = 0) : m • x = 0 := by
  have hc : IsCoprime ((p : ℤ) ^ a) t := IsCoprime.pow_left ht
  obtain ⟨u, v, huv⟩ := hc
  have h₁' : ((m : ℤ) * (p : ℤ) ^ a) • x = 0 := by exact_mod_cast h₁
  have : (m : ℤ) • x = 0 := by
    have e : (m : ℤ) = u * ((m : ℤ) * (p : ℤ) ^ a) + v * ((m : ℤ) * t) := by
      linear_combination (-(m : ℤ)) * huv
    rw [e, add_smul, mul_smul u, mul_smul v, h₁', h₂, smul_zero, smul_zero, add_zero]
  exact_mod_cast this

end M4aHerbrand.DescAlg

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ exists_fundamentalClass_ideleClassGroup exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp"
namespace DescBridge
p2m_open "M4aHerbrand"

theorem zmultiples_eq_top_of_span_eq_top {M : Type*} [AddCommGroup M] (inst : Module ℤ M) (g : M)
    (h : @Submodule.span ℤ M _ _ inst {g} = ⊤) : AddSubgroup.zmultiples g = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro x
  have hx : x ∈ @Submodule.span ℤ M _ _ inst {g} := by rw [h]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (@Submodule.mem_span_singleton ℤ M _ _ inst x g).1 hx
  exact ⟨a, (int_smul_eq_zsmul inst a g).symm.trans ha⟩

theorem span_eq_top_of_zmultiples_eq_top {M : Type*} [AddCommGroup M] (inst : Module ℤ M) (g : M)
    (h : AddSubgroup.zmultiples g = ⊤) : @Submodule.span ℤ M _ _ inst {g} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x ∈ AddSubgroup.zmultiples g := by rw [h]; exact AddSubgroup.mem_top x
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  exact (@Submodule.mem_span_singleton ℤ M _ _ inst x g).2 ⟨a, (int_smul_eq_zsmul inst a g).trans ha⟩

theorem span_eq_top_transfer {M : Type*} [AddCommGroup M] (i₁ i₂ : Module ℤ M) (g : M)
    (h : @Submodule.span ℤ M _ _ i₁ {g} = ⊤) : @Submodule.span ℤ M _ _ i₂ {g} = ⊤ :=
  span_eq_top_of_zmultiples_eq_top i₂ g (zmultiples_eq_top_of_span_eq_top i₁ g h)

theorem mem_span_of_span_eq_top {M : Type*} [AddCommGroup M] (i₁ i₂ : Module ℤ M) (g x : M)
    (h : @Submodule.span ℤ M _ _ i₁ {g} = ⊤) : x ∈ @Submodule.span ℤ M _ _ i₂ {g} := by
  rw [span_eq_top_transfer i₁ i₂ g h]; exact Submodule.mem_top

end M4aHerbrand.DescBridge

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ exists_fundamentalClass_ideleClassGroup exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp"
namespace DescPlumb
p2m_open "M4aHerbrand"

variable (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
  [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
  (W : HeightOneSpectrum (𝓞 F'))

noncomputable def iD (r : ↥(NumberField.PlaceDecomp.decomp E F' W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : (W.under (𝓞 F)).adicCompletion F),
      HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (r σ • x) =
        σ • HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) x) :
    Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (HeightOneSpectrum.Extension.adicCompletionSemialgHom F F'
      (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) : (W.under (𝓞 F)).adicCompletion F →* W.adicCompletion F'))).toIntLinearMap,
    fun σ => LinearMap.ext fun a => by
      have key : ∀ u : ((W.under (𝓞 F)).adicCompletion F)ˣ,
          Units.map (HeightOneSpectrum.Extension.adicCompletionSemialgHom F F'
              (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) : (W.under (𝓞 F)).adicCompletion F →* W.adicCompletion F') (r σ • u) =
            σ • Units.map (HeightOneSpectrum.Extension.adicCompletionSemialgHom F F'
              (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) : (W.under (𝓞 F)).adicCompletion F →* W.adicCompletion F') u :=
        fun u => Units.ext (by
          simp only [Units.coe_map, MonoidHom.coe_coe, NumberField.PlaceDecomp.coe_smul_units]
          exact hr σ _)
      exact congrArg Additive.ofMul (key (Additive.toMul a))⟩

omit [NumberField E] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F'] in
theorem iD_apply (r : ↥(NumberField.PlaceDecomp.decomp E F' W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : (W.under (𝓞 F)).adicCompletion F),
      HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (r σ • x) =
        σ • HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) x)
    (x : ((W.under (𝓞 F)).adicCompletion F)ˣ) :
    ((Additive.toMul ((iD E F F' W r hr).hom (Additive.ofMul x)) : (W.adicCompletion F')ˣ) : W.adicCompletion F') =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (x : (W.under (𝓞 F)).adicCompletion F) :=
  rfl

omit [IsGalois E F] [IsGalois E F'] in

theorem natCard_eq_natCard_ker_mul {G H : Type} [Group G] [Group H] [Finite G] (r : G →* H) (hr : Function.Surjective r) :
    Nat.card G = Nat.card ↥r.ker * Nat.card H := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hr).toEquiv, mul_comm,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem exists_restrict_iD :
    ∃ (r : ↥(NumberField.PlaceDecomp.decomp E F' W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
      (iD : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ),
      Function.Surjective r ∧

      (∀ σ : ↥(NumberField.PlaceDecomp.decomp E F' W),
        ((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) = AlgEquiv.restrictNormalHom F (σ : F' ≃ₐ[E] F')) ∧
      (∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : F),
        algebraMap F F' (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : F' ≃ₐ[E] F') (algebraMap F F' x)) ∧

      ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).comp (NumberField.PlaceDecomp.decomp E F' W).subtype =
        (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype.comp r) ∧

      (∃ hle : NumberField.PlaceDecomp.decomp E F' W ≤
          (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)),
        r = ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap
              (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))).comp (Subgroup.inclusion hle)) ∧

      (∀ σ : ↥(NumberField.PlaceDecomp.decomp E F' W), r σ = 1 ↔ ∀ x : F, (σ : F' ≃ₐ[E] F') (algebraMap F F' x) = algebraMap F F' x) ∧

      (∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
        ((Additive.toMul (iD.hom (Additive.ofMul x)) : (W.adicCompletion F')ˣ) : W.adicCompletion F') =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (x : (W.under (𝓞 F)).adicCompletion F)) ∧

      (∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : (W.under (𝓞 F)).adicCompletion F),
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (r σ • x) =
          σ • HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) x) ∧
      Nat.card ↥(NumberField.PlaceDecomp.decomp E F' W) = Nat.card ↥r.ker * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := by
  obtain ⟨r, hsurj, hcoe, hker, -, hsemi⟩ :=
    NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F F' W
  have hle : NumberField.PlaceDecomp.decomp E F' W ≤
      (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) :=
    fun σ hσ => by
      rw [Subgroup.mem_comap, ← hcoe ⟨σ, hσ⟩]
      exact SetLike.coe_mem _
  refine ⟨r, iD E F F' W r hsemi, hsurj, hcoe, fun σ x => ?_, ?_, ⟨hle, ?_⟩, hker, fun x => rfl, hsemi,
    natCard_eq_natCard_ker_mul r hsurj⟩
  · rw [hcoe]
    exact AlgEquiv.restrictNormal_commutes (σ : F' ≃ₐ[E] F') F x
  · exact MonoidHom.ext fun σ => (hcoe σ).symm
  · exact MonoidHom.ext fun σ => Subtype.ext (hcoe σ)

end M4aHerbrand.DescPlumb

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ exists_fundamentalClass_ideleClassGroup exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp"
namespace DescPlumb
p2m_open "M4aHerbrand"

variable (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
  [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
  (W : HeightOneSpectrum (𝓞 F'))

omit [NumberField F'] [IsGalois E F] [IsGalois E F'] in

theorem exists_above (w : HeightOneSpectrum (𝓞 F)) : ∃ W : HeightOneSpectrum (𝓞 F'), W.under (𝓞 F) = w :=
  ⟨NumberField.PlaceAbove.above F F' w, HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above F F' w)⟩

omit [IsGalois E F] [IsGalois E F'] in

theorem faithfulSMul_of_bridge {G : Type} [Group G] {X Y : Type} [MulAction G X] [SMul G Y] [FaithfulSMul G X]
    (Φ : X ≃ Y) (hΦ : ∀ (g : G) (x : X), Φ (g • x) = g • Φ x) : FaithfulSMul G Y :=
  ⟨fun {g₁ g₂} h => eq_of_smul_eq_smul fun x : X => Φ.injective (by rw [hΦ, hΦ, h])⟩

theorem exists_tower_reading
    (r : ↥(NumberField.PlaceDecomp.decomp E F' W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : F), algebraMap F F' (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : F' ≃ₐ[E] F') (algebraMap F F' x))
    (iW : Rep.res r (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F' W) (W.adicCompletion F')ˣ)
    (hiW : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iW.hom (Additive.ofMul x)) : (W.adicCompletion F')ˣ) : W.adicCompletion F') =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (x : (W.under (𝓞 F)).adicCompletion F))

    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) L'] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) (↥L')ˣ]
    (Φ : (W.under (𝓞 F)).adicCompletion F ≃+* L')
    (h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : (W.under (𝓞 F)).adicCompletion F), Φ (g • x) = g • Φ x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hB : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) K₀)
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
    (hθ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F) = Φ.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) (↥L')ˣ))
    (hu' : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) K₀ u') :
    ∃ (qU : ℕ) (_ : Fact qU.Prime) (LU : IntermediateField ℚ_[qU] (PadicAlgCl qU)) (_ : FiniteDimensional ℚ_[qU] LU)
      (_ : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F' W) LU) (_ : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F' W) (↥LU)ˣ)
      (ΦU : W.adicCompletion F' ≃+* LU)
      (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : ℚ_[qU]), g • algebraMap ℚ_[qU] LU x = algebraMap ℚ_[qU] LU x)
      (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' W)) (v : (↥LU)ˣ), ((g • v : (↥LU)ˣ) : LU) = g • (v : LU))
      (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : W.adicCompletion F'), ΦU (g • x) = g • ΦU x)
      (KU : IntermediateField ℚ_[qU] (PadicAlgCl qU)) (_ : FiniteDimensional ℚ_[qU] KU)
      (_ : ExtCitation.LocalLevel.IsBase qU LU ↥(NumberField.PlaceDecomp.decomp E F' W) KU)
      (θU : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F' W) (↥LU)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F' W) (W.adicCompletion F')ˣ)
      (_ : ∀ v : (↥LU)ˣ, ((Additive.toMul (θU.hom (Additive.ofMul v)) : (W.adicCompletion F')ˣ) : W.adicCompletion F') = ΦU.symm (v : LU))
      (uU : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F' W) (↥LU)ˣ))
      (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass qU LU ↥(NumberField.PlaceDecomp.decomp E F' W) KU uU)
      (n : ℕ),
      (groupCohomology.map r iW 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ 2).hom u') =
        n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' W)) θU 2).hom uU ∧
      Nat.card ↥(NumberField.PlaceDecomp.decomp E F' W) = n * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ∧ 0 < n := by
  classical

  obtain ⟨qU, instF, L, LU, hLL, fdL, fdLU, actL, ffL, actLu, actU, ffU, actUu, Φt, ΦU, h3t, h3U, h1t, h1U, h2t, h2U, hcompat, -⟩ :=
    NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower E F F' W
  haveI : Fact qU.Prime := instF
  letI := actL; letI := actLu; letI := actU; letI := actUu
  haveI := fdL; haveI := fdLU; haveI := ffL; haveI := ffU

  have hsolvU : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F' W) :=
    ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic qU LU ↥(NumberField.PlaceDecomp.decomp E F' W) h1U
  have hsolvL : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) :=
    ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic qU L ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) h1t

  obtain ⟨KU, fdKU, θt, θU, ut, uU, hBt, hBU, hθt, hθU, hut, huU, hid, hcard⟩ :=
    NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower E F F' W hsolvU hsolvL r hr iW hiW
      qU L LU hLL Φt ΦU h3t h3U h1t h1U h2t h2U hcompat
  haveI := fdKU

  have hqw : ((q : ℕ) : 𝓞 F) ∈ (W.under (𝓞 F)).asIdeal :=
    (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F (W.under (𝓞 F)) q L' Φ).2
  have hqUw : ((qU : ℕ) : 𝓞 F) ∈ (W.under (𝓞 F)).asIdeal :=
    (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F (W.under (𝓞 F)) qU L Φt).2
  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ((W.under (𝓞 F)).adicCompletion F) := NumberField.PlaceDecomp.faithfulSMul_decomp E F (W.under (𝓞 F))
  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) L' := faithfulSMul_of_bridge Φ.toEquiv h3
  have hind := NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E F (W.under (𝓞 F))
      q hqw L' Φ h1 h2 h3 K₀ hB θ hθ u' hu' qU hqUw L Φt h1t h2t h3t KU hBt θt hθt ut hut
  refine ⟨qU, instF, LU, fdLU, actU, actUu, ΦU, h1U, h2U, h3U, KU, fdKU, hBU, θU, hθU, uU, huU, Nat.card ↥r.ker, ?_, hcard, Nat.card_pos⟩
  rw [hind]
  exact hid

end M4aHerbrand.DescPlumb

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ exists_fundamentalClass_ideleClassGroup exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp"
namespace DescInjH
p2m_open "M4aHerbrand"

theorem isZero_H1_res_of_injective {G K : Type} [Group G] [Group K] (ι : K →* G) (hι : Function.Injective ι) (A : Rep ℤ G)
    (h : Limits.IsZero (groupCohomology (Rep.res ι.range.subtype A) 1)) :
    Limits.IsZero (groupCohomology (Rep.res ι A) 1) := by
  let e : K ≃* ↥ι.range := MonoidHom.ofInjective hι
  have he : ∀ k : K, ((e k : ↥ι.range) : G) = ι k := fun k => MonoidHom.ofInjective_apply hι
  have he' : ∀ y : ↥ι.range, ι (e.symm y) = (y : G) := fun y => by rw [← he, MulEquiv.apply_symm_apply]
  haveI : Subsingleton (groupCohomology (Rep.res ι A) 1) := by
    refine ⟨fun a b => ?_⟩
    rw [← sub_eq_zero]
    induction (a - b) using groupCohomology.H1_induction_on with
    | _ f =>
      rw [groupCohomology.H1π_eq_zero_iff]
      have hf := (groupCohomology.mem_cocycles₁_iff (A := Rep.res ι A) (f : K → A)).mp f.2

      let f' : ↥ι.range → A := fun y => f (e.symm y)
      have hf' : f' ∈ groupCohomology.cocycles₁ (Rep.res ι.range.subtype A) := by
        rw [groupCohomology.mem_cocycles₁_iff]
        intro y₁ y₂
        have := hf (e.symm y₁) (e.symm y₂)
        rw [← map_mul] at this
        change f (e.symm (y₁ * y₂)) = A.ρ (y₁ : G) (f (e.symm y₂)) + f (e.symm y₁)
        rw [this]
        change A.ρ (ι (e.symm y₁)) (f (e.symm y₂)) + f (e.symm y₁) = _
        rw [he']

      have h0 : (ConcreteCategory.hom (groupCohomology.H1π (Rep.res ι.range.subtype A))) ⟨f', hf'⟩ = 0 := by
        set x := (ConcreteCategory.hom (groupCohomology.H1π (Rep.res ι.range.subtype A))) ⟨f', hf'⟩
        have hm : ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ x) = 0 := Limits.IsZero.eq_of_tgt h _ _
        have := congrArg (fun φ => (ModuleCat.Hom.hom φ) (1 : ℤ)) hm
        simpa using this
      rw [groupCohomology.H1π_eq_zero_iff] at h0
      obtain ⟨a, ha⟩ := h0

      refine ⟨a, funext fun k => ?_⟩
      have := congrFun ha (e k)
      rw [groupCohomology.d₀₁_hom_apply] at this ⊢
      change A.ρ ((e k : ↥ι.range) : G) a - a = f (e.symm (e k)) at this
      rw [he, MulEquiv.symm_apply_apply] at this
      exact this
  exact ModuleCat.isZero_of_subsingleton _

noncomputable def jH (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
    (w : HeightOneSpectrum (𝓞 F))
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶
      Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) :
    Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F w))
        (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) ⟶
      Rep.res ((NumberField.PlaceDecomp.decomp E F w).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
        (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) :=
  Rep.ofHom
    { toLinearMap := (Rep.Hom.hom j).toLinearMap
      isIntertwining' := fun h => (Rep.Hom.hom j).isIntertwining' (h : F' ≃ₐ[E] F') }

theorem jH_hom_apply (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
    (w : HeightOneSpectrum (𝓞 F))
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶
      Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))
    (c : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) :
    (jH E F F' w j).hom c = j.hom c := rfl

theorem injective_map_jH (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
    (w : HeightOneSpectrum (𝓞 F))
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶
      Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))
    (hjinj : Function.Injective j.hom)
    (hjim : ∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'),
      (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
        (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom)
    (h1 : ∀ S : Subgroup (F' ≃ₐ[E] F'), Limits.IsZero
      (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 1)) :
    Function.Injective (groupCohomology.map
      ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F w))
      (jH E F F' w j) 2).hom := by
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite ℚ E F'
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  haveI : Fintype ↥((NumberField.PlaceDecomp.decomp E F w).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) :=
    Fintype.ofFinite _
  refine groupCohomology.map_two_injective_of_injective_of_isZero_H1_ker _
    (MonoidHom.subgroupComap_surjective_of_surjective _ _ (AlgEquiv.restrictNormalHom_surjective F')) _ _ (jH E F F' w j)
    hjinj ?_ ?_
  ·
    intro c' hc'
    apply hjim c'
    intro g' hg'
    have hmem : g' ∈ (NumberField.PlaceDecomp.decomp E F w).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) := by
      rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hg']
      exact one_mem _
    have := hc' ⟨g', hmem⟩ (by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (MonoidHom.mem_ker).mp hg')
    exact this
  ·
    have hι : Function.Injective
        (((NumberField.PlaceDecomp.decomp E F w).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype.comp
          ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F w)).ker.subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    exact isZero_H1_res_of_injective _ hι _ (h1 _)

end M4aHerbrand.DescInjH

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (lam' : ∀ w : HeightOneSpectrum (𝓞 F'),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hlam' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      (lam' w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' w x) : IdeleClassGroup (𝓞 F') F'))
    (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))
    (hj : ∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
      Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') x) : IdeleClassGroup (𝓞 F') F'))
    (hjinj : Function.Injective j.hom)
    (hjim : ∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'), (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
      (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom)
    (uF' : groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2)
    (hord' : ∀ k : ℤ, k • uF' = 0 ↔ (Nat.card (F' ≃ₐ[E] F') : ℤ) ∣ k)
    (hloc' : ∀ (w : HeightOneSpectrum (𝓞 F'))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F' w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ]
        (Φ : w.adicCompletion F' ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : w.adicCompletion F'), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F')ˣ) : w.adicCompletion F') = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) (lam' w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F' w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom uF') :
    ∃ uF : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      (∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S) ∧
      (∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF} = ⊤) ∧
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
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF) ∧
      (groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom uF = Module.finrank F F' • uF' := by
  classical
  have hp : p.Prime := Fact.out

  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite ℚ E F'
  haveI : FiniteDimensional F F' := Module.Finite.of_restrictScalars_finite ℚ F F'
  have hπs : Function.Surjective (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) :=
    AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := F) (E := F')
  have hcardG : Nat.card (F ≃ₐ[E] F) = Module.finrank E F := IsGalois.card_aut_eq_finrank E F
  have hcardG' : Nat.card (F' ≃ₐ[E] F') = Module.finrank E F' := IsGalois.card_aut_eq_finrank E F'
  have htower : Module.finrank E F * Module.finrank F F' = Module.finrank E F' := Module.finrank_mul_finrank E F F'
  have hn : Module.finrank E F ≠ 0 := Module.finrank_pos.ne'
  have hN : Module.finrank F F' ≠ 0 := Module.finrank_pos.ne'

  obtain ⟨u₀, _, hcardS, hspanS⟩ := M4aHerbrand.exists_fundamentalClass_ideleClassGroup E F D hact
  obtain ⟨_, h1S', _, _⟩ := M4aHerbrand.exists_fundamentalClass_ideleClassGroup E F' D' hact'
  obtain ⟨u₁, hcardF, hspanF⟩ := M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup E F D hact
  obtain ⟨g', hcardF', hspanF'⟩ := M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup E F' D' hact'
  have hinj : Function.Injective
      (groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom :=
    groupCohomology.map_two_injective_of_injective_of_isZero_H1_ker
      (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) hπs _ _ j hjinj hjim (h1S' _)

  have hordu₁ : ∀ k : ℤ, k • u₁ = 0 ↔ ((Module.finrank E F : ℕ) : ℤ) ∣ k :=
    M4aHerbrand.DescAlg.zsmul_eq_zero_iff_dvd_of_span_eq_top u₁ _ hn (hcardF.trans hcardG)
      (M4aHerbrand.DescBridge.span_eq_top_transfer _ _ u₁ hspanF)
  have hordg' : ∀ k : ℤ, k • g' = 0 ↔ ((Module.finrank E F * Module.finrank F F' : ℕ) : ℤ) ∣ k := by
    rw [htower]
    exact M4aHerbrand.DescAlg.zsmul_eq_zero_iff_dvd_of_span_eq_top g' _ Module.finrank_pos.ne' (hcardF'.trans hcardG')
      (M4aHerbrand.DescBridge.span_eq_top_transfer _ _ g' hspanF')
  have hordu' : ∀ k : ℤ, k • uF' = 0 ↔ ((Module.finrank E F * Module.finrank F F' : ℕ) : ℤ) ∣ k := by
    rw [htower, ← hcardG']
    exact hord'
  obtain ⟨d, hd, hdeq⟩ := M4aHerbrand.DescAlg.exists_isCoprime_map_zsmul_eq_nsmul
    (groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom.toAddMonoidHom
    hinj _ _ hn hN u₁ hordu₁ g' (M4aHerbrand.DescBridge.span_eq_top_transfer _ _ g' hspanF') hordg' uF' hordu'

  refine ⟨d • u₁, hcardS, ?_, ?_, ?_⟩
  ·
    intro S
    haveI : Fintype S := Fintype.ofFinite S
    have hgen₁ := M4aHerbrand.DescAlg.span_singleton_map_eq_top_of_mem
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom.toAddMonoidHom
      u₀ u₁ (M4aHerbrand.DescBridge.span_eq_top_transfer _ _ _ (hspanS S))
      (M4aHerbrand.DescBridge.mem_span_of_span_eq_top _ _ u₁ u₀ hspanF)
    have hS : Fintype.card S ∣ Module.finrank E F := by
      rw [← hcardG, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card S
    have hgen := M4aHerbrand.DescAlg.span_singleton_zsmul_eq_top _ _ _ Fintype.card_ne_zero (hcardS S) hS hgen₁ d hd
    rw [LinearMap.toAddMonoidHom_coe, ← map_zsmul] at hgen
    exact M4aHerbrand.DescBridge.span_eq_top_transfer _ _ _ hgen
  ·
    intro w q _ L' _ _ _ Φ h1 h2 h3 K₀ _ hB θ hθ u' hu' m a hm hma

    obtain ⟨W, rfl⟩ := M4aHerbrand.DescPlumb.exists_above F F' w

    obtain ⟨r, iW, hrs, hrcoe, hr, hsq, ⟨hle, hrH⟩, hker, hiW, hiWsmul, hcardD'⟩ :=
      M4aHerbrand.DescPlumb.exists_restrict_iD E F F' W

    obtain ⟨q'', iq'', L'', iL'', iMS'', iMD'', Φ'', h1'', h2'', h3'', K₀'', iK'', hB'', θ'', hθ'', u'', hu'', n, hread, hcardn, hnpos⟩ :=
      M4aHerbrand.DescPlumb.exists_tower_reading E F F' W r hr iW hiW q L' Φ h1 h2 h3 K₀ hB θ hθ u' hu'

    obtain ⟨k₀, b, hk₀, hkb⟩ := M4aHerbrand.DescAlg.exists_coprime_mul_pow_eq p n hp hnpos.ne'
    obtain ⟨hm'', hma''⟩ := M4aHerbrand.DescAlg.coprime_mul_and_mul_pow_add_eq p hm hk₀ hma hkb hcardn

    have hlocW := hloc' W q'' L'' Φ'' h1'' h2'' h3'' K₀'' hB'' θ'' hθ'' u'' hu'' (m * k₀) (a + b) hm'' hma''

    let z : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ((W.under (𝓞 F)).adicCompletion F)ˣ) 2 :=
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ 2).hom u'
    let y : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2 := n • (groupCohomology.map ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (𝟙 (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom uF'
    let κ : Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶ Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) :=
      (Rep.resFunctor ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))).map (lam (W.under (𝓞 F))) ≫ M4aHerbrand.DescInjH.jH E F F' (W.under (𝓞 F)) j
    let φW : (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F' W) (W.adicCompletion F')ˣ) ⟶ Rep.res (Subgroup.inclusion hle) (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) := lam' W
    have hκ : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ, κ.hom (Additive.ofMul x) =
        Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι (W.under (𝓞 F)) x)) : IdeleClassGroup (𝓞 F') F') := by
      intro x
      show j.hom ((lam (W.under (𝓞 F))).hom (Additive.ofMul x)) = _
      rw [hlam]
      exact hj _
    have hφW : ∀ x : (W.adicCompletion F')ˣ, φW.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' W x) : IdeleClassGroup (𝓞 F') F') :=
      fun x => hlam' W x

    have hresres : ∀ v : groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2,
        (groupCohomology.map (Subgroup.inclusion hle) (𝟙 (Rep.res (Subgroup.inclusion hle) (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))))) 2).hom ((groupCohomology.map ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (𝟙 (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom v) =
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F' W).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F' W).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom v := by
      intro v
      induction v using groupCohomology.H2_induction_on with
      | h c => simp only [groupCohomology.H2π_comp_map_apply]; rfl

    have hy : ((m * k₀ : ℕ) : ℤ) • (groupCohomology.map (Subgroup.inclusion hle)
            (𝟙 (Rep.res (Subgroup.inclusion hle) (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))))) 2).hom y =
          ((m * k₀ : ℕ) : ℤ) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' W)) φW 2).hom ((groupCohomology.map r iW 2).hom z) := by
      have h' := congrArg (fun t => n • t) hlocW
      try simp only at h'
      simp only [y, z, map_nsmul, hresres, hread, natCast_zsmul]
      rw [smul_comm (m * k₀) n, smul_comm (m * k₀) n]
      exact h'.symm

    have hS2 := M4aHerbrand.zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp E F F' D' hact' ι' hι' ι hι W r hr hle iW hiW κ hκ φW hφW ((m * k₀ : ℕ) : ℤ) z y hy

    have hidx : ((NumberField.PlaceDecomp.decomp E F' W).subgroupOf ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))).index * n = Module.finrank F F' := by
      haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := Fintype.ofFinite _
      have hD0 : Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ≠ 0 := Nat.card_pos.ne'
      have h1 := Subgroup.index_mul_card ((NumberField.PlaceDecomp.decomp E F' W).subgroupOf ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))
      have h2 : Nat.card ↥((NumberField.PlaceDecomp.decomp E F' W).subgroupOf ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' W) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      have h3 := Subgroup.index_mul_card ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))
      have h4 : ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).index = (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).index := Subgroup.index_comap_of_surjective _ hπs
      have h5 := Subgroup.index_mul_card (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))
      have h6 : Nat.card (F' ≃ₐ[E] F') = Nat.card (F ≃ₐ[E] F) * Module.finrank F F' := by
        rw [hcardG, hcardG', htower]

      have hH : Nat.card ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) = Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) * Module.finrank F F' := by
        have hi0 : (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hi0)
        rw [← h4] at h5 ⊢
        rw [h3, h6, ← h5, h4, mul_assoc]
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hD0)
      rw [mul_assoc, ← hcardn, ← h2, h1, hH, mul_comm]

    have hdeq' : (groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom (d • u₁) = ((Module.finrank F F' : ℕ) : ℤ) • uF' := hdeq
    have hRHS : (((NumberField.PlaceDecomp.decomp E F' W).subgroupOf ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))).index : ℤ) • y =
        (groupCohomology.map ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (𝟙 (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom ((groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom (d • u₁)) := by
      rw [hdeq', map_zsmul]
      simp only [y]
      rw [← natCast_zsmul, smul_smul, ← Nat.cast_mul, hidx]

    have hsqr : ∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
        (groupCohomology.map ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (𝟙 (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom ((groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom x) =
          (groupCohomology.map ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (M4aHerbrand.DescInjH.jH E F F' (W.under (𝓞 F)) j) 2).hom ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) := by
      intro x
      induction x using groupCohomology.H2_induction_on with
      | h c => simp only [groupCohomology.H2π_comp_map_apply]; rfl

    have hκfac : ∀ x : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ((W.under (𝓞 F)).adicCompletion F)ˣ) 2,
        (groupCohomology.map ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) κ 2).hom x =
          (groupCohomology.map ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (M4aHerbrand.DescInjH.jH E F F' (W.under (𝓞 F)) j) 2).hom
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (lam (W.under (𝓞 F))) 2).hom x) := by
      intro x
      induction x using groupCohomology.H2_induction_on with
      | h c => simp only [groupCohomology.H2π_comp_map_apply]; rfl

    have hJ := M4aHerbrand.DescInjH.injective_map_jH E F F' (W.under (𝓞 F)) j hjinj hjim h1S'
    have key : ((m * k₀ : ℕ) : ℤ) • ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (lam (W.under (𝓞 F))) 2).hom z -
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom (d • u₁)) = 0 := by
      apply hJ
      rw [map_zsmul, map_sub, map_zero, zsmul_sub, ← hκfac, hS2, hRHS, hsqr, sub_self]

    have hcardX : (m * p ^ a) • ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (lam (W.under (𝓞 F))) 2).hom z -
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom (d • u₁)) = 0 := by
      haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := Fintype.ofFinite _
      rw [hma, Nat.card_eq_fintype_card, ← hcardS (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (addOrderOf_dvd_natCard _)
    rw [natCast_zsmul] at key
    have hmX := M4aHerbrand.DescAlg.nsmul_eq_zero_of_mul_pow_nsmul_of_mul_coprime_nsmul _ p m a k₀ hp hk₀ hcardX key
    rw [← sub_eq_zero, ← nsmul_sub]
    exact hmX
  ·
    have : (groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom (d • u₁) =
        ((Module.finrank F F' : ℕ) : ℤ) • uF' := hdeq
    rw [this, natCast_zsmul]

end S_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two
end P2MW
export P2MW.S_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two (solution)
