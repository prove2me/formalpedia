-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7c9635c4-ee14-56aa-abb8-1e9b662c5fa0

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict

set_option autoImplicit false

open Polynomial IsLocalRing

namespace S17Lift

variable {L : Type*} [Field L]

theorem one_sub_dvd_natCast_of_pow_eq_one {R : Type*} [CommRing R] [IsDomain R]
    {η : R} {n : ℕ} (hη : η ^ n = 1) (hη1 : η ≠ 1) : (1 - η) ∣ (n : R) := by

  have h0 : (∑ i ∈ Finset.range n, η ^ i) = 0 := by
    have h := geom_sum_mul η n
    rw [hη, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hη1)
  have h1 : (∑ i ∈ Finset.range n, (1 : R) ^ i) = n := by simp
  have hd := Polynomial.sub_dvd_eval_sub (1 : R) η (∑ i ∈ Finset.range n, (X : R[X]) ^ i)
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X] at hd
  rwa [h0, h1, sub_zero] at hd

end S17Lift

open S17Lift in
theorem solution
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] [CharP k q] (red : A →+* k)
    (S : Finset k) (hS : ∀ a ∈ S, a ^ (q ^ 2) = a) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₀),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ K₀, σ x = x) ∧
      ∀ a ∈ S, a ∈ Set.range (ModularCurve.NodeLocalized.redRestrict red K₀) := by
  classical
  have hq : q.Prime := Fact.out
  set Ω := AlgebraicClosure ℚ with hΩ

  set n : ℕ := q ^ 2 - 1 with hn
  have hq2 : 2 ≤ q := hq.two_le
  have hn0 : n ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  haveI : NeZero n := ⟨hn0⟩

  have hqA : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hu.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at h1
    exact not_isUnit_zero h1
  have hnunit : IsUnit ((n : ℕ) : ↥A) := by
    by_contra hnu
    have h1 : ((n : ℕ) : ↥A) ∈ maximalIdeal ↥A := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have h2 : ((q ^ 2 : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      rw [Nat.cast_pow]; exact Ideal.pow_mem_of_mem _ hqA 2 (by norm_num)
    have h3 : (1 : ↥A) ∈ maximalIdeal ↥A := by
      have h12 := sub_mem h2 h1
      have : ((q ^ 2 : ℕ) : ↥A) - (n : ↥A) = 1 := by
        rw [hn, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_one]; ring
      rwa [this] at h12
    exact (maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)

  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
    haveI : NeZero ((n : ℕ) : Ω) := NeZero.charZero
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic n Ω) (degree_cyclotomic_pos n Ω (Nat.pos_of_ne_zero hn0)).ne'
    exact ⟨ζ, (isRoot_cyclotomic_iff.mp hζ)⟩
  have hζA : ∀ i : ℕ, ζ ^ i ∈ A := by
    intro i
    apply ValuationSubring.mem_of_valuation_le_one
    have h : (A.valuation (ζ ^ i)) ^ n = 1 := by
      rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, map_one]
    exact not_lt.mp fun hlt => (one_lt_pow₀ hlt hn0).ne' h

  have hunit : ∀ i j : ℕ, ζ ^ i ≠ ζ ^ j → IsUnit ((⟨ζ ^ i, hζA i⟩ : ↥A) - ⟨ζ ^ j, hζA j⟩) := by
    intro i j hij

    let η : ↥A := ⟨ζ ^ (j + (n - 1) * i), hζA _⟩
    have hηn : η ^ n = 1 := by
      apply Subtype.ext
      simp only [η, SubmonoidClass.mk_pow, OneMemClass.coe_one]
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hzi : (⟨ζ ^ i, hζA i⟩ : ↥A) * η = ⟨ζ ^ j, hζA j⟩ := by
      apply Subtype.ext
      simp only [η, MulMemClass.coe_mul]
      rw [← pow_add, show i + (j + (n - 1) * i) = j + n * i by
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        zify [this]; ring]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hη1 : η ≠ 1 := by
      intro h
      apply hij
      have := hzi
      rw [h, mul_one] at this
      exact congrArg Subtype.val this
    have hdvd : (1 - η) ∣ ((n : ℕ) : ↥A) := one_sub_dvd_natCast_of_pow_eq_one hηn hη1
    have hu1 : IsUnit (1 - η) := isUnit_of_dvd_unit hdvd hnunit
    have hui : IsUnit (⟨ζ ^ i, hζA i⟩ : ↥A) := by
      refine isUnit_of_dvd_unit ⟨⟨ζ ^ ((n - 1) * i), hζA _⟩, ?_⟩ isUnit_one
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
      rw [← pow_add, show i + (n - 1) * i = n * i by
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        zify [this]; ring, pow_mul, hζ.pow_eq_one, one_pow]
    have : (⟨ζ ^ i, hζA i⟩ : ↥A) - ⟨ζ ^ j, hζA j⟩ = ⟨ζ ^ i, hζA i⟩ * (1 - η) := by
      rw [mul_sub, mul_one, hzi]
    rw [this]
    exact hui.mul hu1

  have hζint : IsIntegral ℚ ζ := (hζ.isIntegral (Nat.pos_of_ne_zero hn0)).tower_top
  let K₀ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ ↥K₀ := IntermediateField.adjoin.finiteDimensional hζint
  refine ⟨K₀, inferInstance, ?_, ?_⟩
  ·
    intro σ hσ x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ

    have hdζ : ((d.1 : Ω ≃ₐ[ℚ] Ω)) ζ = ζ := by

      set σ' : Ω ≃ₐ[ℚ] Ω := (d.1 : Ω ≃ₐ[ℚ] Ω) with hσ'
      have hpow : (σ' ζ) ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hpow

      have hres : residue ↥A (d • ⟨ζ, by simpa using hζA 1⟩) = residue ↥A ⟨ζ, by simpa using hζA 1⟩ := by
        rw [ResidueField.residue_smul]
        have hker := hd
        rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hker
        exact congrArg (fun f : IsLocalRing.ResidueField ↥A ≃+* IsLocalRing.ResidueField ↥A => f (residue ↥A ⟨ζ, _⟩)) hker
      have hval : ((d • (⟨ζ, by simpa using hζA 1⟩ : ↥A) : ↥A) : Ω) = σ' ζ := rfl
      by_contra hne
      have hne' : ζ ^ i ≠ ζ ^ 1 := by rw [pow_one, hi]; exact hne
      have hu := hunit i 1 hne'

      have hmem : ((⟨ζ ^ i, hζA i⟩ : ↥A) - ⟨ζ ^ 1, hζA 1⟩) ∈ maximalIdeal ↥A := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
        have e1 : (⟨ζ ^ i, hζA i⟩ : ↥A) = d • ⟨ζ, by simpa using hζA 1⟩ := by
          apply Subtype.ext
          show ζ ^ i = ((d • (⟨ζ, by simpa using hζA 1⟩ : ↥A) : ↥A) : Ω)
          rw [hval]; exact hi
        have e2 : (⟨ζ ^ 1, hζA 1⟩ : ↥A) = ⟨ζ, by simpa using hζA 1⟩ := by
          apply Subtype.ext; simp
        rw [e1, e2]
        exact hres
      exact (mem_maximalIdeal _ |>.mp hmem) hu

    have hle : K₀ ≤ IntermediateField.fixedField (Subgroup.zpowers ((d.1 : Ω ≃ₐ[ℚ] Ω))) := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      show ζ ∈ IntermediateField.fixedField _
      rw [IntermediateField.mem_fixedField_iff]
      rintro g ⟨m, rfl⟩
      dsimp only
      have hfix' : ((d.1 : Ω ≃ₐ[ℚ] Ω)).symm ζ = ζ := by
        rw [AlgEquiv.symm_apply_eq]; exact hdζ.symm
      induction m using Int.induction_on with
      | zero => simp
      | succ m ih => rw [zpow_add_one, AlgEquiv.mul_apply, hdζ]; exact ih
      | pred m ih => rw [zpow_sub_one, AlgEquiv.mul_apply, show ((d.1 : Ω ≃ₐ[ℚ] Ω))⁻¹ = ((d.1 : Ω ≃ₐ[ℚ] Ω)).symm from rfl, hfix']; exact ih
    have := (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) _ (Subgroup.mem_zpowers _)
    exact this
  ·
    intro a ha
    by_cases ha0 : a = 0
    · exact ⟨0, by rw [map_zero, ha0]⟩
    have han : a ^ n = 1 := by
      have h := hS a ha
      have : a ^ (q ^ 2) = a ^ n * a := by
        rw [← pow_succ, hn, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
      rw [this] at h
      exact mul_left_injective₀ ha0 (by simpa using h)

    have hζK : ∀ i : ℕ, ζ ^ i ∈ K₀ := fun i =>
      pow_mem (IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)) i
    have hζAK : ∀ i : ℕ, ζ ^ i ∈ ModularCurve.NodeLocalized.coeffSubring A K₀ := fun i =>
      ⟨hζA i, hζK i⟩
    let z : ℕ → ↥(ModularCurve.NodeLocalized.coeffSubring A K₀) := fun i => ⟨ζ ^ i, hζAK i⟩
    have hred : ∀ i, ModularCurve.NodeLocalized.redRestrict red K₀ (z i) = red ⟨ζ ^ i, hζA i⟩ := fun i => rfl

    have hinj : Set.InjOn (fun i : ℕ => red ⟨ζ ^ i, hζA i⟩) (Finset.range n : Set ℕ) := by
      intro i hi j hj hij
      dsimp only at hij
      by_contra hne
      have hne' : ζ ^ i ≠ ζ ^ j := by
        intro h
        exact hne (hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h)
      have hu := (hunit i j hne').map red
      rw [map_sub, hij, sub_self] at hu
      exact not_isUnit_zero hu

    let T : Finset k := (Finset.range n).image (fun i : ℕ => red ⟨ζ ^ i, hζA i⟩)
    have hTcard : T.card = n := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hTsub : T ⊆ Polynomial.nthRootsFinset n (1 : k) := by
      intro b hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
      rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0), ← map_pow]
      have : (⟨ζ ^ i, hζA i⟩ : ↥A) ^ n = 1 := by
        apply Subtype.ext
        simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      rw [this, map_one]
    have hcard_le : (Polynomial.nthRootsFinset n (1 : k)).card ≤ n := by
      rw [Polynomial.nthRootsFinset_def]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
    have hTeq : T = Polynomial.nthRootsFinset n (1 : k) :=
      Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard]; exact hcard_le)
    have haT : a ∈ T := by
      rw [hTeq, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0)]
      exact han
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp haT
    exact ⟨z i, by rw [hred, hi]⟩

end S_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict (solution)
