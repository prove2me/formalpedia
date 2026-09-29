-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/15edafb7-4887-5be6-a65c-2253990f5214

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild
import Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative
import Theorems.Thm_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField
import Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
import Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
import Theorems.Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
import Theorems.Thm_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
import Theorems.Thm_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
import Theorems.Thm_IsDiscreteValuationRing_finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsLocalRing

namespace GRDev

section Helpers

variable {B : Type*} [CommRing B]

lemma sub_one_mul_mem_pow {I : Ideal B} {n : ℕ} {x y : B} (hx : x - 1 ∈ I ^ n) (hy : y - 1 ∈ I ^ n) :
    x * y - 1 ∈ I ^ n := by
  have : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [this]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) hy

lemma sub_mul_mem_pow_of_sub_one {I : Ideal B} {n : ℕ} {a c u : B} (hac : a - c ∈ I ^ n) (hu : u - 1 ∈ I ^ n) :
    a - c * u ∈ I ^ n := by
  have : a - c * u = (a - c) - c * (u - 1) := by ring
  rw [this]; exact Ideal.sub_mem _ hac (Ideal.mul_mem_left _ _ hu)

lemma exists_eq_mul_of_sub_mem_pow {I : Ideal B} {n : ℕ} {a c : B} (hc : IsUnit c) (hac : a - c ∈ I ^ n) :
    ∃ u : B, a = c * u ∧ u - 1 ∈ I ^ n := by
  obtain ⟨c, rfl⟩ := hc
  refine ⟨↑c⁻¹ * a, by rw [← mul_assoc, Units.mul_inv, one_mul], ?_⟩
  have : (↑c⁻¹ * a - 1 : B) = ↑c⁻¹ * (a - c) := by rw [mul_sub, Units.inv_mul]
  rw [this]; exact Ideal.mul_mem_left _ _ hac

lemma finprod_sub_one_mem_pow {ι : Type*} [Finite ι] {I : Ideal B} {n : ℕ} (f : ι → B) (hf : ∀ i, f i - 1 ∈ I ^ n) :
    (∏ᶠ i, f i) - 1 ∈ I ^ n := by
  classical
  have hfin := Fintype.ofFinite ι
  rw [finprod_eq_prod_of_fintype]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact sub_one_mul_mem_pow (hf i) ih

variable {G : Type*} [Group G] [MulSemiringAction G B]

lemma smul_eq_self_of_subgroup {H : Subgroup G} {a : B} (ha : ∀ g : G, g • a = a) (h : H) : h • a = a := ha h

lemma coe_quotient_smul_fixedPoints (H : Subgroup G) [H.Normal] (g : G) (x : FixedPoints.subring B H) :
    (((QuotientGroup.mk g : G ⧸ H) • x : FixedPoints.subring B H) : B) = g • (x : B) := rfl

lemma forall_quotient_smul_eq_iff (H : Subgroup G) [H.Normal] (x : FixedPoints.subring B H) :
    (∀ c : G ⧸ H, c • x = x) ↔ ∀ g : G, g • (x : B) = x := by
  constructor
  · intro h g; exact congrArg Subtype.val (h (QuotientGroup.mk g))
  · intro h c; induction c using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (h g)

variable [Finite G]

noncomputable def normFixed (H : Subgroup G) (b : B) : FixedPoints.subring B H :=
  ⟨∏ᶠ h : H, h • b, fun h' => by
    rw [smul_finprod']
    exact finprod_eq_of_bijective (fun h => h' * h) (Group.mulLeft_bijective h') fun h => (mul_smul _ _ _).symm⟩

@[scoped simp] lemma coe_normFixed (H : Subgroup G) (b : B) : (normFixed H b : B) = ∏ᶠ h : H, h • b := rfl

lemma finprod_smul_eq_finprod_quotient_smul_normFixed (H : Subgroup G) [H.Normal] (b : B) :
    ∏ᶠ g : G, g • b = ((∏ᶠ c : G ⧸ H, c • normFixed H b : FixedPoints.subring B H) : B) := by
  classical
  have hG := Fintype.ofFinite G
  have hH := Fintype.ofFinite H
  have hQ := Fintype.ofFinite (G ⧸ H)
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, SubmonoidClass.coe_finsetProd,
    ← Finset.prod_fiberwise Finset.univ (QuotientGroup.mk (s := H)) (fun g : G => g • b)]
  refine Finset.prod_congr rfl fun c _ => ?_
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective c
  rw [coe_quotient_smul_fixedPoints, coe_normFixed, finprod_eq_prod_of_fintype, Finset.smul_prod']
  have hfil : (Finset.univ.filter fun g : G => (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g₀) =
      Finset.univ.image fun h : H => g₀ * h := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [QuotientGroup.eq]
    constructor
    · intro hg; exact ⟨⟨g₀⁻¹ * g, by simpa using H.inv_mem hg⟩, by simp⟩
    · rintro ⟨h, rfl⟩; simp [h.2]
  rw [hfil, Finset.prod_image (fun h₁ _ h₂ _ hh => Subtype.ext (mul_left_cancel hh))]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [Subgroup.smul_def, ← mul_smul]

end Helpers

section DVRHelpers

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

lemma mem_maximalIdeal_pow_iff_le_addVal (x : B) (n : ℕ) :
    x ∈ maximalIdeal B ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal B x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  simp

variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]

lemma mem_pow_fixedPoints_iff [FaithfulSMul G B] [IsDiscreteValuationRing (FixedPoints.subring B G)]
    [(maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) (B ⧸ maximalIdeal B)]
    (z : FixedPoints.subring B G) (j : ℕ) :
    z ∈ maximalIdeal (FixedPoints.subring B G) ^ j ↔ (z : B) ∈ maximalIdeal B ^ (lowerRamificationCard B G 0 * j) := by
  rw [mem_maximalIdeal_pow_iff_le_addVal, mem_maximalIdeal_pow_iff_le_addVal,
    IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints z]
  have he : lowerRamificationCard B G 0 ≠ 0 := (lowerRamificationCard_pos 0).ne'
  generalize IsDiscreteValuationRing.addVal (FixedPoints.subring B G) z = v
  induction v using ENat.recTopCoe with
  | top =>
    have htop : (lowerRamificationCard B G 0 : ℕ∞) * ⊤ = ⊤ := WithTop.mul_top (Nat.cast_ne_zero.mpr he)
    rw [htop]
    simp
  | coe k =>
    rw [show ((lowerRamificationCard B G 0 : ℕ) : ℕ∞) * (k : ℕ∞) = ((lowerRamificationCard B G 0 * k : ℕ) : ℕ∞) by push_cast; rfl]
    rw [ENat.coe_le_coe, ENat.coe_le_coe]
    exact ⟨fun h => Nat.mul_le_mul_left _ h, fun h => Nat.le_of_mul_le_mul_left h (Nat.pos_of_ne_zero he)⟩

omit [IsDomain B] [IsDiscreteValuationRing B] [Finite G] in

lemma lowerRamificationGroup_subgroup [IsLocalRing B] (H : Subgroup G) (i : ℕ) :
    lowerRamificationGroup B H i = (lowerRamificationGroup B G i).subgroupOf H := by
  ext h
  simp only [mem_lowerRamificationGroup, Subgroup.mem_subgroupOf]
  rfl

omit [IsDomain B] [IsDiscreteValuationRing B] in

lemma liesOver_fixedPoints [IsLocalRing B] :
    (maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B G)) :=
  ⟨FixedPoints.maximalIdeal_subring_eq_comap⟩

omit [IsDomain B] [IsDiscreteValuationRing B] [Finite G] in

lemma faithfulSMul_subgroup [FaithfulSMul G B] (H : Subgroup G) : FaithfulSMul H B :=
  ⟨fun {h₁ h₂} hh => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := B) hh)⟩

omit [IsDomain B] [IsDiscreteValuationRing B] in

lemma finite_residue_fixedPoints [IsLocalRing B] [Finite (B ⧸ maximalIdeal B)] :
    Finite (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) := by
  have : Finite (ResidueField B) := ‹Finite (B ⧸ maximalIdeal B)›
  have hf : Finite (ResidueField (FixedPoints.subring B G)) :=
    Finite.of_injective (ResidueField.map (FixedPoints.subring B G).subtype)
      (ResidueField.map (FixedPoints.subring B G).subtype).injective
  exact hf

omit [IsDomain B] [IsDiscreteValuationRing B] [Finite G] in

lemma isSeparable_residue_of_finite [IsLocalRing B]
    [(maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B G))]
    [Finite (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G))] [Finite (B ⧸ maximalIdeal B)] :
    Algebra.IsSeparable (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) (B ⧸ maximalIdeal B) := by
  letI : Field (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) := Ideal.Quotient.field _
  letI : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field _
  have : Module.Finite (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) (B ⧸ maximalIdeal B) :=
    Module.Finite.of_finite
  have : Algebra.IsAlgebraic (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) (B ⧸ maximalIdeal B) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end DVRHelpers

section Herbrand

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]

lemma upperRamificationIndex_eq_of_herbrandPhi_eq {n m : ℕ} (h : herbrandPhi R G n = m) :
    upperRamificationIndex R G m = n := by
  unfold upperRamificationIndex
  have hmem : n ∈ {k : ℕ | (m : ℚ) ≤ herbrandPhi R G k} := by simp [h]
  apply le_antisymm (Nat.sInf_le hmem)
  by_contra hlt
  rw [not_le] at hlt
  have hmem' := Nat.sInf_mem ⟨n, hmem⟩
  simp only [Set.mem_setOf_eq] at hmem'
  have := herbrandPhi_strictMono (R := R) (G := G) (show ((sInf {k : ℕ | (m : ℚ) ≤ herbrandPhi R G k} : ℕ) : ℚ) < n by
    exact_mod_cast hlt)
  rw [h] at this
  exact absurd (hmem'.trans_lt this) (lt_irrefl _)

lemma upperRamificationGroup_eq_of_herbrandPhi_eq {n m : ℕ} (h : herbrandPhi R G n = m) :
    upperRamificationGroup R G m = lowerRamificationGroup R G n := by
  unfold upperRamificationGroup; rw [upperRamificationIndex_eq_of_herbrandPhi_eq h]

lemma lowerRamificationCard_of_prime_of_le {t : ℕ} (ht : lowerRamificationGroup R G t = ⊤) {i : ℕ} (hi : i ≤ t) :
    lowerRamificationCard R G i = Nat.card G := by
  unfold lowerRamificationCard
  have : lowerRamificationGroup R G i = ⊤ := top_le_iff.mp (ht ▸ lowerRamificationGroup_antitone hi)
  rw [this, Subgroup.card_top]

lemma lowerRamificationCard_of_prime_of_lt {t : ℕ} (ht' : lowerRamificationGroup R G (t + 1) = ⊥) {i : ℕ} (hi : t < i) :
    lowerRamificationCard R G i = 1 := by
  unfold lowerRamificationCard
  have : lowerRamificationGroup R G i = ⊥ := le_bot_iff.mp (ht' ▸ lowerRamificationGroup_antitone (Nat.succ_le_of_lt hi))
  rw [this, Subgroup.card_bot]

lemma herbrandPhi_of_le_jump {t : ℕ} (ht : lowerRamificationGroup R G t = ⊤) {n : ℕ} (hn : n ≤ t) :
    herbrandPhi R G n = n := by
  rw [herbrandPhi_natCast]
  have h0 : lowerRamificationCard R G 0 = Nat.card G := lowerRamificationCard_of_prime_of_le ht (Nat.zero_le _)
  have hA : ∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ) = (n : ℚ) * Nat.card G := by
    rw [Finset.sum_eq_card_nsmul (b := (Nat.card G : ℚ)) fun i hi => by
      rw [lowerRamificationCard_of_prime_of_le ht ((Finset.mem_Icc.mp hi).2.trans hn)]]
    rw [Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  rw [hA, h0]
  have : (Nat.card G : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  field_simp

lemma herbrandPhi_jump_add_card_mul {t : ℕ} (ht : lowerRamificationGroup R G t = ⊤)
    (ht' : lowerRamificationGroup R G (t + 1) = ⊥) (j : ℕ) :
    herbrandPhi R G ((t + Nat.card G * j : ℕ) : ℚ) = t + j := by
  rw [herbrandPhi_natCast]
  have h0 : lowerRamificationCard R G 0 = Nat.card G := lowerRamificationCard_of_prime_of_le ht (Nat.zero_le _)
  have hsplit : Finset.Icc 1 (t + Nat.card G * j) = Finset.Icc 1 t ∪ Finset.Ioc t (t + Nat.card G * j) := by
    ext i; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 t) (Finset.Ioc t (t + Nat.card G * j)) := by
    rw [Finset.disjoint_left]; intro i hi hi'; simp only [Finset.mem_Icc, Finset.mem_Ioc] at hi hi'; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hA : ∑ i ∈ Finset.Icc 1 t, (lowerRamificationCard R G i : ℚ) = (t : ℚ) * Nat.card G := by
    rw [Finset.sum_eq_card_nsmul (b := (Nat.card G : ℚ)) fun i hi => by
      rw [lowerRamificationCard_of_prime_of_le ht (Finset.mem_Icc.mp hi).2]]
    rw [Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hB : ∑ i ∈ Finset.Ioc t (t + Nat.card G * j), (lowerRamificationCard R G i : ℚ) = (Nat.card G : ℚ) * j := by
    rw [Finset.sum_eq_card_nsmul (b := (1 : ℚ)) fun i hi => by
      rw [lowerRamificationCard_of_prime_of_lt ht' (Finset.mem_Ioc.mp hi).1]; simp]
    rw [Nat.card_Ioc, nsmul_eq_mul, Nat.add_sub_cancel_left]; push_cast; ring
  rw [hA, hB, h0]
  have : (Nat.card G : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  field_simp

def psiPrime (ℓ t y : ℕ) : ℕ := if y ≤ t then y else t + ℓ * (y - t)

lemma herbrandPhi_psiPrime {t : ℕ} (ht : lowerRamificationGroup R G t = ⊤)
    (ht' : lowerRamificationGroup R G (t + 1) = ⊥) (y : ℕ) :
    herbrandPhi R G (psiPrime (Nat.card G) t y : ℕ) = y := by
  unfold psiPrime
  split_ifs with hy
  · exact herbrandPhi_of_le_jump ht hy
  · rw [herbrandPhi_jump_add_card_mul ht ht', Nat.cast_sub (not_le.mp hy).le]; ring

lemma le_psiPrime {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (t y : ℕ) : y ≤ psiPrime ℓ t y := by
  unfold psiPrime; split_ifs with h
  · exact le_rfl
  · have := Nat.le_mul_of_pos_left (y - t) hℓ; omega

lemma psiPrime_mono {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (t : ℕ) {y y' : ℕ} (h : y ≤ y') : psiPrime ℓ t y ≤ psiPrime ℓ t y' := by
  unfold psiPrime; split_ifs with h1 h2 h2
  · exact h
  · have := Nat.le_mul_of_pos_left (y' - t) hℓ; omega
  · omega
  · have := Nat.mul_le_mul_left ℓ (show y - t ≤ y' - t by omega); omega

end Herbrand

section Counting

variable {G : Type*} [Group G]

lemma card_eq_card_map_mul_card_subgroupOf [Finite G] (H : Subgroup G) [H.Normal] (X : Subgroup G) :
    Nat.card X = Nat.card (X.map (QuotientGroup.mk' H)) * Nat.card (X.subgroupOf H) := by
  classical
  let f : X →* G ⧸ H := (QuotientGroup.mk' H).domRestrict X
  have hker : f.ker = H.subgroupOf X := by
    ext x; simp [f, Subgroup.mem_subgroupOf]
  have hrange : f.range = X.map (QuotientGroup.mk' H) := MonoidHom.domRestrict_range X (QuotientGroup.mk' H)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker]
  congr 1
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨(g : X).1, Subgroup.mem_subgroupOf.mp g.2⟩, Subgroup.mem_subgroupOf.mpr (g : X).2⟩
      invFun := fun h => ⟨⟨(h : H).1, Subgroup.mem_subgroupOf.mp h.2⟩, Subgroup.mem_subgroupOf.mpr (h : H).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma normal_of_isMulCommutative [IsMulCommutative G] (H : Subgroup G) : H.Normal :=
  ⟨fun a ha g => by rwa [IsMulCommutative.is_comm.comm g a, mul_inv_cancel_right]⟩

lemma isMulCommutative_quotient [IsMulCommutative G] (H : Subgroup G) [H.Normal] : IsMulCommutative (G ⧸ H) :=
  ⟨⟨fun a b => by
    induction a using QuotientGroup.induction_on with | H x =>
    induction b using QuotientGroup.induction_on with | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, IsMulCommutative.is_comm.comm x y]⟩⟩

lemma exists_subgroup_card_prime [Finite G] (h : Nat.card G ≠ 1) :
    ∃ H : Subgroup G, (Nat.card H).Prime := by
  classical
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hpd
  exact ⟨Subgroup.zpowers g, by rw [Nat.card_zpowers, hg]; exact hp⟩

end Counting

section Transport

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]

lemma exists_jump_of_prime (H : Subgroup G) (hℓ : (Nat.card H).Prime) (hH0 : lowerRamificationGroup B H 0 = ⊤) :
    ∃ t : ℕ, lowerRamificationGroup B H t = ⊤ ∧ lowerRamificationGroup B H (t + 1) = ⊥ := by
  classical
  haveI : FaithfulSMul H B := faithfulSMul_subgroup H
  haveI : Fact (Nat.card H).Prime := ⟨hℓ⟩
  haveI : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [show Nat.card H = Nat.card H from rfl]; exact hℓ.one_lt)

  have hbot : ∃ N : ℕ, lowerRamificationGroup B H N = ⊥ := by
    by_contra hall
    push Not at hall
    have htop : ∀ N, lowerRamificationGroup B H N = ⊤ := fun N =>
      (Subgroup.eq_bot_or_eq_top_of_prime_card _).resolve_left (hall N)
    have hsep : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    have h := IsLocalRing.iInf_lowerRamificationGroup_eq_bot (R := B) (G := H) hsep
    simp only [htop, iInf_top] at h
    exact top_ne_bot h
  let P : ℕ → Prop := fun i => lowerRamificationGroup B H (i + 1) = ⊥
  have hex : ∃ i, P i := by obtain ⟨N, hN⟩ := hbot; exact ⟨N, le_bot_iff.mp (hN ▸ lowerRamificationGroup_antitone (Nat.le_succ N))⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩

  have hne : lowerRamificationGroup B H (Nat.find hex) ≠ ⊥ := by
    rcases h : Nat.find hex with _ | i
    · rw [hH0]; exact top_ne_bot
    · have := Nat.find_min hex (m := i) (by omega)
      exact this
  exact (Subgroup.eq_bot_or_eq_top_of_prime_card _).resolve_left hne

variable [(maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B G))]
  [Algebra.IsSeparable (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) (B ⧸ maximalIdeal B)]

lemma herbrandPhi_psiPrime_eq_of_quotient (H : Subgroup G) [H.Normal] {t : ℕ}
    (ht : lowerRamificationGroup B H t = ⊤) (ht' : lowerRamificationGroup B H (t + 1) = ⊥)
    {k' m : ℕ} (hk' : herbrandPhi (FixedPoints.subring B H) (G ⧸ H) k' = m) :
    herbrandPhi B G (psiPrime (Nat.card H) t k' : ℕ) = m := by
  rw [IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
      (R := B) (G := G) (S := FixedPoints.subring B H) (H := H)
      (fun n => IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField n)
      (Nat.cast_nonneg _)]
  rw [herbrandPhi_psiPrime ht ht' k', hk']

lemma lowerRamificationGroup_quotient_zero_eq_top (H : Subgroup G) [H.Normal] (h0 : lowerRamificationGroup B G 0 = ⊤) :
    lowerRamificationGroup (FixedPoints.subring B H) (G ⧸ H) 0 = ⊤ := by
  have := IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField (R := B) (G := G) (H := H) 0
  rw [h0, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective H)] at this
  rw [Nat.cast_zero, herbrandPhi_zero, Nat.ceil_zero] at this
  exact this.symm

lemma card_upperRamificationGroup_eq (H : Subgroup G) [H.Normal] (j : ℕ) :
    Nat.card (upperRamificationGroup B G j) =
      Nat.card (upperRamificationGroup (FixedPoints.subring B H) (G ⧸ H) j) *
        Nat.card ((upperRamificationGroup B G j).subgroupOf H) := by
  rw [card_eq_card_map_mul_card_subgroupOf H,
    IsDiscreteValuationRing.upperRamificationQuotientCompat_of_isSeparable_residueField (R := B) (G := G) H j
      (Nat.cast_nonneg j)]

end Transport

section More

variable {B : Type*} [CommRing B]

lemma sub_mem_pow_of_sub_mul_mem {I : Ideal B} {n : ℕ} {a x u : B} (h : a - x * u ∈ I ^ n) (hu : u - 1 ∈ I ^ n) :
    a - x ∈ I ^ n := by
  have : a - x = (a - x * u) + x * (u - 1) := by ring
  rw [this]; exact Ideal.add_mem _ h (Ideal.mul_mem_left _ _ hu)

variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]

lemma isUnit_smul' (g : G) {b : B} (hb : IsUnit b) : IsUnit (g • b) :=
  hb.map (MulSemiringAction.toRingHom G B g)

lemma isUnit_finprod_smul {b : B} (hb : IsUnit b) : IsUnit (∏ᶠ g : G, g • b) := by
  classical
  have := Fintype.ofFinite G
  rw [finprod_eq_prod_of_fintype]
  exact IsUnit.prod_univ_iff.mpr fun g => isUnit_smul' g hb

lemma smul_finprod_smul (g : G) (b : B) : g • ∏ᶠ g' : G, g' • b = ∏ᶠ g' : G, g' • b := by
  rw [smul_finprod']
  exact finprod_eq_of_bijective (fun g' => g * g') (Group.mulLeft_bijective g) fun g' => (mul_smul _ _ _).symm

end More

def Conclusion (B : Type*) [CommRing B] [IsLocalRing B] (G : Type*) [Group G] [MulSemiringAction G B] (e m : ℕ) : Prop :=
  (∃ S : Finset B,
      S.card * Nat.card (upperRamificationGroup B G ((m + 1 : ℕ) : ℚ)) ≤ Nat.card (upperRamificationGroup B G (m : ℚ)) ∧
      (∀ s ∈ S, IsUnit s ∧ ∀ g : G, g • s = s) ∧
      ∀ a : B, IsUnit a → (∀ g : G, g • a = a) → a - 1 ∈ maximalIdeal B ^ (e * m) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧ b - 1 ∈ maximalIdeal B ^ upperRamificationIndex B G m ∧
          a - s * ∏ᶠ g : G, g • b ∈ maximalIdeal B ^ (e * (m + 1))) ∧
  (∀ u : B, IsUnit u → u - 1 ∈ maximalIdeal B ^ (upperRamificationIndex B G m + 1) →
      (∏ᶠ g : G, g • u) - 1 ∈ maximalIdeal B ^ (e * (m + 1))) ∧
  (∃ k : ℕ, herbrandPhi B G k = m)

theorem conclusion_of_card_eq_one
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] (hG : Nat.card G = 1) (m : ℕ) :
    Conclusion B G (Nat.card G) m := by
  classical
  haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG).1
  haveI : Unique G := uniqueOfSubsingleton 1
  have hall : ∀ i, lowerRamificationGroup B G i = ⊤ := fun i => Subsingleton.elim _ _
  have hφ : herbrandPhi B G m = m := herbrandPhi_of_le_jump (hall m) le_rfl
  have hk : upperRamificationIndex B G m = m := upperRamificationIndex_eq_of_herbrandPhi_eq hφ
  have hN : ∀ b : B, ∏ᶠ g : G, g • b = b := fun b => by rw [finprod_unique, Subsingleton.elim (default : G) 1, one_smul]
  have hcard : ∀ X : Subgroup G, Nat.card X = 1 := fun X => by
    rw [Subsingleton.elim X ⊤, Subgroup.card_top, hG]
  refine ⟨⟨{1}, by rw [Finset.card_singleton, one_mul, hcard, hcard], by simp, fun a ha _ ham => ⟨1, by simp, a, ha, by rw [hk]; simpa [hG] using ham, ?_⟩⟩,
    fun u _ hu => by rw [hN]; simpa [hG, hk] using hu, ⟨m, hφ⟩⟩
  rw [hN, one_mul, sub_self, hG]; exact Ideal.zero_mem _

theorem conclusion_of_totallyRamified (n : ℕ) :
    ∀ (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
      (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B] [IsMulCommutative G]
      [(maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B G))]
      [Algebra.IsSeparable (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) (B ⧸ maximalIdeal B)]
      [Finite (B ⧸ maximalIdeal B)],
      Nat.card G = n → lowerRamificationGroup B G 0 = ⊤ → ∀ m : ℕ, Conclusion B G (Nat.card G) m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B _ _ _ G _ _ _ _ _ _ _ _ hn h0 m
    classical
    by_cases htriv : Nat.card G = 1
    · exact conclusion_of_card_eq_one htriv m

    obtain ⟨H, hℓ⟩ := exists_subgroup_card_prime htriv
    haveI : H.Normal := normal_of_isMulCommutative H
    haveI : Fact (Nat.card H).Prime := ⟨hℓ⟩

    haveI : FaithfulSMul H B := faithfulSMul_subgroup H
    haveI : (maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B H)) := liesOver_fixedPoints
    haveI : Finite (FixedPoints.subring B H ⧸ maximalIdeal (FixedPoints.subring B H)) := finite_residue_fixedPoints
    haveI : Algebra.IsSeparable (FixedPoints.subring B H ⧸ maximalIdeal (FixedPoints.subring B H)) (B ⧸ maximalIdeal B) :=
      isSeparable_residue_of_finite
    haveI : IsDiscreteValuationRing (FixedPoints.subring B H) := FixedPoints.isDiscreteValuationRing_subring

    haveI : PerfectField (ResidueField B) := by
      haveI : Finite (ResidueField B) := ‹Finite (B ⧸ maximalIdeal B)›
      infer_instance
    haveI : FaithfulSMul (G ⧸ H) (FixedPoints.subring B H) :=
      (FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring (R := B) (G := G) H).1
    haveI : (maximalIdeal (FixedPoints.subring B H)).LiesOver
        (maximalIdeal (FixedPoints.subring (FixedPoints.subring B H) (G ⧸ H))) := liesOver_fixedPoints
    haveI : Finite (FixedPoints.subring (FixedPoints.subring B H) (G ⧸ H) ⧸
        maximalIdeal (FixedPoints.subring (FixedPoints.subring B H) (G ⧸ H))) := finite_residue_fixedPoints
    haveI : Algebra.IsSeparable (FixedPoints.subring (FixedPoints.subring B H) (G ⧸ H) ⧸
        maximalIdeal (FixedPoints.subring (FixedPoints.subring B H) (G ⧸ H)))
        (FixedPoints.subring B H ⧸ maximalIdeal (FixedPoints.subring B H)) := isSeparable_residue_of_finite
    haveI : IsMulCommutative (G ⧸ H) := isMulCommutative_quotient H

    have hH0 : lowerRamificationGroup B H 0 = ⊤ := by rw [lowerRamificationGroup_subgroup, h0, Subgroup.top_subgroupOf]
    obtain ⟨t, ht, ht'⟩ := exists_jump_of_prime H hℓ hH0
    have hQ0 := lowerRamificationGroup_quotient_zero_eq_top (B := B) H h0
    have hGcard : Nat.card G = Nat.card (G ⧸ H) * (Nat.card H) := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    have hlt : Nat.card (G ⧸ H) < n := by
      rw [← hn, hGcard]; exact lt_mul_of_one_lt_right Nat.card_pos hℓ.one_lt
    have IH := ih _ hlt (FixedPoints.subring B H) (G ⧸ H) rfl hQ0
    obtain ⟨⟨S', hS'c, hS'u, hmain'⟩, hN2', k', hk'⟩ := IH m
    obtain ⟨-, -, k'', hk''⟩ := IH (m + 1)

    have hφ : herbrandPhi B G (psiPrime (Nat.card H) t k' : ℕ) = m := herbrandPhi_psiPrime_eq_of_quotient H ht ht' hk'
    have hφ1 : herbrandPhi B G (psiPrime (Nat.card H) t k'' : ℕ) = (m + 1 : ℕ) := by
      have := herbrandPhi_psiPrime_eq_of_quotient (B := B) H ht ht' (k' := k'') (m := m + 1) (by exact_mod_cast hk'')
      exact_mod_cast this
    have hkG : upperRamificationIndex B G m = psiPrime (Nat.card H) t k' := upperRamificationIndex_eq_of_herbrandPhi_eq hφ
    have hkQ : upperRamificationIndex (FixedPoints.subring B H) (G ⧸ H) m = k' :=
      upperRamificationIndex_eq_of_herbrandPhi_eq hk'
    have hGm : upperRamificationGroup B G (m : ℚ) = lowerRamificationGroup B G (psiPrime (Nat.card H) t k') :=
      upperRamificationGroup_eq_of_herbrandPhi_eq hφ
    have hGm1 : upperRamificationGroup B G ((m + 1 : ℕ) : ℚ) = lowerRamificationGroup B G (psiPrime (Nat.card H) t k'') :=
      upperRamificationGroup_eq_of_herbrandPhi_eq hφ1
    have hk'lt : k' < k'' := by
      have h1 : herbrandPhi (FixedPoints.subring B H) (G ⧸ H) k' < herbrandPhi (FixedPoints.subring B H) (G ⧸ H) k'' := by
        rw [hk']; push_cast at hk'' ⊢; rw [hk'']; exact lt_add_one _
      exact_mod_cast (herbrandPhi_strictMono.lt_iff_lt).mp h1

    have heH : lowerRamificationCard B H 0 = (Nat.card H) := by unfold lowerRamificationCard; rw [hH0, Subgroup.card_top]
    have hdict : ∀ (z : FixedPoints.subring B H) (j : ℕ),
        z ∈ maximalIdeal (FixedPoints.subring B H) ^ j ↔ (z : B) ∈ maximalIdeal B ^ ((Nat.card H) * j) := fun z j => by
      rw [mem_pow_fixedPoints_iff, heH]

    obtain ⟨SH, hSHc, hSHu, hrung⟩ :=
      IsDiscreteValuationRing.exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
        (B := B) (G := H) hℓ t ht ht' k'

    let NQ : B → B := fun y => if hy : ∀ h : H, h • y = y then
      ((∏ᶠ c : G ⧸ H, c • (⟨y, hy⟩ : FixedPoints.subring B H) : FixedPoints.subring B H) : B) else 1
    have hNQ : ∀ (y : B) (hy : ∀ h : H, h • y = y),
        NQ y = ((∏ᶠ c : G ⧸ H, c • (⟨y, hy⟩ : FixedPoints.subring B H) : FixedPoints.subring B H) : B) :=
      fun y hy => dif_pos hy
    refine ⟨⟨Finset.image₂ (fun x y => x * NQ y) (S'.image (↑)) SH, ?_, ?_, ?_⟩, ?_, ⟨psiPrime (Nat.card H) t k', hφ⟩⟩
    ·
      have hsub : ∀ j : ℕ, Nat.card ((upperRamificationGroup B G j).subgroupOf H) =
          Nat.card (lowerRamificationGroup B H (upperRamificationIndex B G j)) := fun j => by
        rw [lowerRamificationGroup_subgroup]; rfl
      have hcm := card_upperRamificationGroup_eq (B := B) H m
      have hcm1 := card_upperRamificationGroup_eq (B := B) H (m + 1)
      rw [hsub] at hcm hcm1
      rw [hkG] at hcm
      rw [upperRamificationIndex_eq_of_herbrandPhi_eq hφ1] at hcm1

      have hHlev : SH.card * Nat.card (lowerRamificationGroup B H (psiPrime (Nat.card H) t k'')) ≤
          Nat.card (lowerRamificationGroup B H (psiPrime (Nat.card H) t k')) := by
        by_cases hkt : k' = t
        · have h1 : lowerRamificationGroup B H (psiPrime (Nat.card H) t k') = ⊤ := by
            rw [hkt]; unfold psiPrime; rw [if_pos le_rfl]; exact ht
          have h2 : lowerRamificationGroup B H (psiPrime (Nat.card H) t k'') = ⊥ :=
            le_bot_iff.mp (ht' ▸ lowerRamificationGroup_antitone
              ((show t + 1 ≤ k'' by omega).trans (le_psiPrime hℓ.one_lt.le t k'')))
          rw [h1, h2, Subgroup.card_top, Subgroup.card_bot, mul_one, if_pos hkt] at *
          simpa [if_pos hkt] using hSHc
        · rw [if_neg hkt] at hSHc
          calc SH.card * Nat.card (lowerRamificationGroup B H (psiPrime (Nat.card H) t k''))
              ≤ 1 * Nat.card (lowerRamificationGroup B H (psiPrime (Nat.card H) t k')) := by
                exact Nat.mul_le_mul hSHc (Subgroup.card_le_of_le (lowerRamificationGroup_antitone
                  (psiPrime_mono hℓ.one_lt.le t hk'lt.le)))
            _ = _ := one_mul _
      calc (Finset.image₂ (fun x y => x * NQ y) (S'.image (↑)) SH).card *
            Nat.card (upperRamificationGroup B G ((m + 1 : ℕ) : ℚ))
          ≤ (S'.card * SH.card) * (Nat.card (upperRamificationGroup (FixedPoints.subring B H) (G ⧸ H) ((m + 1 : ℕ) : ℚ)) *
              Nat.card (lowerRamificationGroup B H (psiPrime (Nat.card H) t k''))) := by
            rw [← hcm1]
            exact Nat.mul_le_mul_right _ ((Finset.card_image₂_le _ _ _).trans
              (Nat.mul_le_mul_right _ Finset.card_image_le))
        _ = (S'.card * Nat.card (upperRamificationGroup (FixedPoints.subring B H) (G ⧸ H) ((m + 1 : ℕ) : ℚ))) *
              (SH.card * Nat.card (lowerRamificationGroup B H (psiPrime (Nat.card H) t k''))) := by ring
        _ ≤ Nat.card (upperRamificationGroup (FixedPoints.subring B H) (G ⧸ H) (m : ℚ)) *
              Nat.card (lowerRamificationGroup B H (psiPrime (Nat.card H) t k')) := Nat.mul_le_mul hS'c hHlev
        _ = Nat.card (upperRamificationGroup B G (m : ℚ)) := hcm.symm
    ·
      intro s hs
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.mp hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyu, hyfix, -⟩ := hSHu y hy
      rw [hNQ y hyfix]
      obtain ⟨hs'u, hs'fix⟩ := hS'u s' hs'
      refine ⟨((FixedPoints.isUnit_subring_iff s').mp hs'u).mul ((FixedPoints.isUnit_subring_iff _).mp
        (isUnit_finprod_smul ((FixedPoints.isUnit_subring_iff _).mpr hyu))), fun g => ?_⟩
      rw [smul_mul', (forall_quotient_smul_eq_iff H s').mp hs'fix g]
      congr 1
      exact (forall_quotient_smul_eq_iff H _).mp (fun c => smul_finprod_smul c _) g
    ·
      intro a ha hfix ham
      let a' : FixedPoints.subring B H := ⟨a, fun h => hfix h⟩
      have ha' : IsUnit a' := (FixedPoints.isUnit_subring_iff a').mpr ha
      have hfix' : ∀ c : G ⧸ H, c • a' = a' := (forall_quotient_smul_eq_iff H a').mpr hfix
      have ham' : a' - 1 ∈ maximalIdeal (FixedPoints.subring B H) ^ (Nat.card (G ⧸ H) * m) := by
        rw [hdict]; push_cast
        rw [show (Nat.card H) * (Nat.card (G ⧸ H) * m) = Nat.card G * m by rw [hGcard]; ring]; exact ham
      obtain ⟨s', hs'S, b', hb'u, hb'1, hab'⟩ := hmain' a' ha' hfix' ham'
      rw [hkQ] at hb'1
      have hb'uB : IsUnit (b' : B) := (FixedPoints.isUnit_subring_iff b').mp hb'u
      have hb'lev : (b' : B) - 1 ∈ maximalIdeal B ^ ((Nat.card H) * k') := (hdict _ _).mp hb'1
      obtain ⟨sH, hsHS, b, hbu, hb1, hbsH⟩ := hrung (b' : B) hb'uB b'.2 hb'lev
      obtain ⟨hsHu, hsHfix, -⟩ := hSHu sH hsHS

      let cc : FixedPoints.subring B H := ⟨sH, hsHfix⟩ * normFixed H b
      have hcc : (cc : B) = sH * ∏ᶠ h : H, h • b := rfl
      have hccu : IsUnit cc := (FixedPoints.isUnit_subring_iff cc).mpr (by rw [hcc]; exact hsHu.mul (isUnit_finprod_smul hbu))
      have hb'cc : b' - cc ∈ maximalIdeal (FixedPoints.subring B H) ^ (k' + 1) := by
        rw [hdict]; push_cast [hcc]; exact hbsH
      obtain ⟨u, hb'eq, hu1⟩ := exists_eq_mul_of_sub_mem_pow hccu hb'cc
      have huu : IsUnit u := isUnit_of_mul_isUnit_right (hb'eq ▸ hb'u)
      have hNu := hN2' u huu (by rw [hkQ]; exact hu1)

      have hexp : (∏ᶠ c : G ⧸ H, c • b') =
          ((∏ᶠ c : G ⧸ H, c • (⟨sH, hsHfix⟩ : FixedPoints.subring B H)) * (∏ᶠ c : G ⧸ H, c • normFixed H b)) *
            ∏ᶠ c : G ⧸ H, c • u := by
        rw [hb'eq, show (cc : FixedPoints.subring B H) = ⟨sH, hsHfix⟩ * normFixed H b from rfl]
        simp only [smul_mul', finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
      rw [hexp, ← mul_assoc, ← mul_assoc] at hab'
      have hab'' := sub_mem_pow_of_sub_mul_mem hab' hNu

      refine ⟨(s' : B) * NQ sH, Finset.mem_image₂.mpr ⟨(s' : B), Finset.mem_image_of_mem _ hs'S, sH, hsHS, rfl⟩,
        b, hbu, ?_, ?_⟩
      · rw [hkG]; exact hb1
      · have := (hdict _ _).mp hab''
        rw [show (Nat.card H) * (Nat.card (G ⧸ H) * (m + 1)) = Nat.card G * (m + 1) by rw [hGcard]; ring] at this
        convert this using 2
        rw [hNQ sH hsHfix, finprod_smul_eq_finprod_quotient_smul_normFixed H b]
        push_cast
        ring
    ·
      intro u hu hu1
      rw [hkG] at hu1
      have h1 := (IsDiscreteValuationRing.finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card
        (B := B) (G := H) hℓ t ht ht' k' u).2 hu1
      have h2 : normFixed H u - 1 ∈ maximalIdeal (FixedPoints.subring B H) ^ (k' + 1) := by
        rw [hdict]; push_cast; exact h1
      have h3 := hN2' (normFixed H u) ((FixedPoints.isUnit_subring_iff _).mpr (isUnit_finprod_smul hu)) (by rw [hkQ]; exact h2)
      have h4 := (hdict _ _).mp h3
      rw [show (Nat.card H) * (Nat.card (G ⧸ H) * (m + 1)) = Nat.card G * (m + 1) by rw [hGcard]; ring] at h4
      convert h4 using 2
      rw [finprod_smul_eq_finprod_quotient_smul_normFixed H u]
      push_cast
      ring

section InertiaSplit

open scoped Pointwise

variable {B : Type*} [CommRing B] [IsLocalRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]

lemma card_lowerRamificationGroup_inertia (i : ℕ) :
    Nat.card (lowerRamificationGroup B (lowerRamificationGroup B G 0) i) = Nat.card (lowerRamificationGroup B G i) := by
  rw [lowerRamificationGroup_subgroup]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (lowerRamificationGroup_antitone (Nat.zero_le i))).toEquiv

lemma herbrandPhi_inertia : herbrandPhi B (lowerRamificationGroup B G 0) = herbrandPhi B G := by
  funext u
  unfold herbrandPhi lowerRamificationCard
  simp only [card_lowerRamificationGroup_inertia]

lemma upperRamificationIndex_inertia (v : ℚ) :
    upperRamificationIndex B (lowerRamificationGroup B G 0) v = upperRamificationIndex B G v := by
  unfold upperRamificationIndex; rw [herbrandPhi_inertia]

lemma card_upperRamificationGroup_inertia (v : ℚ) :
    Nat.card (upperRamificationGroup B (lowerRamificationGroup B G 0) v) = Nat.card (upperRamificationGroup B G v) := by
  unfold upperRamificationGroup; rw [upperRamificationIndex_inertia]; exact card_lowerRamificationGroup_inertia _

lemma smul_sub_one_mem_pow (g : G) {x : B} {n : ℕ} (hx : x - 1 ∈ maximalIdeal B ^ n) : g • x - 1 ∈ maximalIdeal B ^ n := by
  have : g • x - 1 = g • (x - 1) := by rw [smul_sub, smul_one]
  rw [this]
  have hmem : g • (x - 1) ∈ g • (maximalIdeal B ^ n) := Ideal.smul_mem_pointwise_smul g _ _ hx
  rwa [pointwise_smul_maximalIdeal_pow] at hmem

end InertiaSplit

theorem conclusion
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B] [IsMulCommutative G]
    [(maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable (FixedPoints.subring B G ⧸ maximalIdeal (FixedPoints.subring B G)) (B ⧸ maximalIdeal B)]
    [Finite (B ⧸ maximalIdeal B)] (m : ℕ) :
    Conclusion B G (Nat.card (lowerRamificationGroup B G 0)) m := by
  classical
  set I : Subgroup G := lowerRamificationGroup B G 0 with hIdef

  haveI : FaithfulSMul I B := faithfulSMul_subgroup I
  haveI : (maximalIdeal B).LiesOver (maximalIdeal (FixedPoints.subring B I)) := liesOver_fixedPoints
  haveI : Finite (FixedPoints.subring B I ⧸ maximalIdeal (FixedPoints.subring B I)) := finite_residue_fixedPoints
  haveI : Algebra.IsSeparable (FixedPoints.subring B I ⧸ maximalIdeal (FixedPoints.subring B I)) (B ⧸ maximalIdeal B) :=
    isSeparable_residue_of_finite
  haveI : IsDiscreteValuationRing (FixedPoints.subring B I) := FixedPoints.isDiscreteValuationRing_subring
  haveI : IsMulCommutative I := ⟨⟨fun a b => Subtype.ext (IsMulCommutative.is_comm.comm (a : G) b)⟩⟩
  haveI : PerfectField (ResidueField B) := by
    haveI : Finite (ResidueField B) := ‹Finite (B ⧸ maximalIdeal B)›
    infer_instance
  haveI : FaithfulSMul (G ⧸ I) (FixedPoints.subring B I) :=
    (FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring (R := B) (G := G) I).1
  haveI : (maximalIdeal (FixedPoints.subring B I)).LiesOver
      (maximalIdeal (FixedPoints.subring (FixedPoints.subring B I) (G ⧸ I))) := liesOver_fixedPoints
  haveI : Finite (FixedPoints.subring (FixedPoints.subring B I) (G ⧸ I) ⧸
      maximalIdeal (FixedPoints.subring (FixedPoints.subring B I) (G ⧸ I))) := finite_residue_fixedPoints
  haveI : Algebra.IsSeparable (FixedPoints.subring (FixedPoints.subring B I) (G ⧸ I) ⧸
      maximalIdeal (FixedPoints.subring (FixedPoints.subring B I) (G ⧸ I)))
      (FixedPoints.subring B I ⧸ maximalIdeal (FixedPoints.subring B I)) := isSeparable_residue_of_finite

  have hI0 : lowerRamificationGroup B I 0 = ⊤ := by rw [lowerRamificationGroup_subgroup]; exact Subgroup.subgroupOf_self _
  have hQ0 : lowerRamificationGroup (FixedPoints.subring B I) (G ⧸ I) 0 = ⊥ := by
    have := IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField (R := B) (G := G) (H := I) 0
    rw [Nat.cast_zero, herbrandPhi_zero, Nat.ceil_zero] at this
    rw [← this, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have heI : lowerRamificationCard B I 0 = Nat.card I := by unfold lowerRamificationCard; rw [hI0, Subgroup.card_top]
  have hdict : ∀ (z : FixedPoints.subring B I) (j : ℕ),
      z ∈ maximalIdeal (FixedPoints.subring B I) ^ j ↔ (z : B) ∈ maximalIdeal B ^ (Nat.card I * j) := fun z j => by
    rw [mem_pow_fixedPoints_iff, heI]

  obtain ⟨⟨S0, hS0c, hS0u, hmain0⟩, hN20, k0, hk0⟩ := conclusion_of_totallyRamified (Nat.card I) B I rfl hI0 m

  let NQ : B → B := fun y => if hy : ∀ h : I, h • y = y then
    ((∏ᶠ c : G ⧸ I, c • (⟨y, hy⟩ : FixedPoints.subring B I) : FixedPoints.subring B I) : B) else 1
  have hNQ : ∀ (y : B) (hy : ∀ h : I, h • y = y),
      NQ y = ((∏ᶠ c : G ⧸ I, c • (⟨y, hy⟩ : FixedPoints.subring B I) : FixedPoints.subring B I) : B) :=
    fun y hy => dif_pos hy

  have hNQ1 : ∀ (u : FixedPoints.subring B I) (j : ℕ), u - 1 ∈ maximalIdeal (FixedPoints.subring B I) ^ j →
      (∏ᶠ c : G ⧸ I, c • u) - 1 ∈ maximalIdeal (FixedPoints.subring B I) ^ j := fun u j hu =>
    finprod_sub_one_mem_pow _ fun c => smul_sub_one_mem_pow c hu
  refine ⟨⟨S0.image NQ, ?_, ?_, ?_⟩, ?_, ⟨k0, by rw [← herbrandPhi_inertia]; exact hk0⟩⟩
  ·
    have h1 := card_upperRamificationGroup_inertia (B := B) (G := G) ((m + 1 : ℕ) : ℚ)
    have h2 := card_upperRamificationGroup_inertia (B := B) (G := G) (m : ℚ)
    rw [← h1, ← h2]
    exact (Nat.mul_le_mul_right _ Finset.card_image_le).trans hS0c
  ·
    intro s hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hyu, hyfix⟩ := hS0u y hy
    rw [hNQ y hyfix]
    refine ⟨(FixedPoints.isUnit_subring_iff _).mp (isUnit_finprod_smul ((FixedPoints.isUnit_subring_iff _).mpr hyu)),
      fun g => ?_⟩
    exact (forall_quotient_smul_eq_iff I _).mp (fun c => smul_finprod_smul c _) g
  ·
    intro a ha hfix ham
    let a' : FixedPoints.subring B I := ⟨a, fun h => hfix h⟩
    have ha' : IsUnit a' := (FixedPoints.isUnit_subring_iff a').mpr ha
    have hfix' : ∀ c : G ⧸ I, c • a' = a' := (forall_quotient_smul_eq_iff I a').mpr hfix
    have ham' : a' - 1 ∈ maximalIdeal (FixedPoints.subring B I) ^ m := by rw [hdict]; exact ham
    obtain ⟨b₀, hb₀u, hb₀1, hab₀⟩ :=
      IsDiscreteValuationRing.exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
        hQ0 m a' ha' hfix' ham'
    have hb₀uB : IsUnit (b₀ : B) := (FixedPoints.isUnit_subring_iff b₀).mp hb₀u
    obtain ⟨s₀, hs₀S, b, hbu, hb1, hbs₀⟩ := hmain0 (b₀ : B) hb₀uB b₀.2 ((hdict _ _).mp hb₀1)
    obtain ⟨hs₀u, hs₀fix⟩ := hS0u s₀ hs₀S
    let cc : FixedPoints.subring B I := ⟨s₀, hs₀fix⟩ * normFixed I b
    have hcc : (cc : B) = s₀ * ∏ᶠ h : I, h • b := rfl
    have hccu : IsUnit cc := (FixedPoints.isUnit_subring_iff cc).mpr (by rw [hcc]; exact hs₀u.mul (isUnit_finprod_smul hbu))
    have hb₀cc : b₀ - cc ∈ maximalIdeal (FixedPoints.subring B I) ^ (m + 1) := by
      rw [hdict]; push_cast [hcc]; exact hbs₀
    obtain ⟨u, hb₀eq, hu1⟩ := exists_eq_mul_of_sub_mem_pow hccu hb₀cc
    have hNu := hNQ1 u (m + 1) hu1
    have hexp : (∏ᶠ c : G ⧸ I, c • b₀) =
        ((∏ᶠ c : G ⧸ I, c • (⟨s₀, hs₀fix⟩ : FixedPoints.subring B I)) * (∏ᶠ c : G ⧸ I, c • normFixed I b)) *
          ∏ᶠ c : G ⧸ I, c • u := by
      rw [hb₀eq, show (cc : FixedPoints.subring B I) = ⟨s₀, hs₀fix⟩ * normFixed I b from rfl]
      simp only [smul_mul', finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
    rw [hexp] at hab₀
    have hab'' := sub_mem_pow_of_sub_mul_mem hab₀ hNu
    refine ⟨NQ s₀, Finset.mem_image_of_mem _ hs₀S, b, hbu, ?_, ?_⟩
    · rw [← upperRamificationIndex_inertia]; exact hb1
    · have := (hdict _ _).mp hab''
      convert this using 2
      rw [hNQ s₀ hs₀fix, finprod_smul_eq_finprod_quotient_smul_normFixed I b]
      push_cast
      ring
  ·
    intro u hu hu1
    rw [← upperRamificationIndex_inertia] at hu1
    have h1 := hN20 u hu hu1
    have h2 : normFixed I u - 1 ∈ maximalIdeal (FixedPoints.subring B I) ^ (m + 1) := by
      rw [hdict]; exact h1
    have h3 := hNQ1 (normFixed I u) (m + 1) h2
    have h4 := (hdict _ _).mp h3
    convert h4 using 2
    rw [finprod_smul_eq_finprod_quotient_smul_normFixed I u]
    push_cast
    ring

private theorem _root_.IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B] [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)] (m : ℕ) :
    ∃ S : Finset B,
      S.card * Nat.card (IsLocalRing.upperRamificationGroup B G ((m + 1 : ℕ) : ℚ)) ≤
          Nat.card (IsLocalRing.upperRamificationGroup B G (m : ℚ)) ∧
      (∀ s ∈ S, IsUnit s ∧ ∀ σ : G, σ • s = s) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) →
        a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card (IsLocalRing.lowerRamificationGroup B G 0) * m) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧
          b - 1 ∈ IsLocalRing.maximalIdeal B ^ IsLocalRing.upperRamificationIndex B G m ∧
          a - s * ∏ᶠ σ : G, σ • b ∈
            IsLocalRing.maximalIdeal B ^ (Nat.card (IsLocalRing.lowerRamificationGroup B G 0) * (m + 1)) :=
  (GRDev.conclusion m).1

p2m_alias "P2MW.S_IsDiscreteValuationRing_exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow.IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow" "IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow"
end GRDev
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow.GRDev"

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B] [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)] (m : ℕ) :
    ∃ S : Finset B,
      S.card * Nat.card (IsLocalRing.upperRamificationGroup B G ((m + 1 : ℕ) : ℚ)) ≤
          Nat.card (IsLocalRing.upperRamificationGroup B G (m : ℚ)) ∧
      (∀ s ∈ S, IsUnit s ∧ ∀ σ : G, σ • s = s) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) →
        a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card (IsLocalRing.lowerRamificationGroup B G 0) * m) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧
          b - 1 ∈ IsLocalRing.maximalIdeal B ^ IsLocalRing.upperRamificationIndex B G m ∧
          a - s * ∏ᶠ σ : G, σ • b ∈
            IsLocalRing.maximalIdeal B ^ (Nat.card (IsLocalRing.lowerRamificationGroup B G 0) * (m + 1)) :=
  IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow m

end S_IsDiscreteValuationRing_exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow (solution)
