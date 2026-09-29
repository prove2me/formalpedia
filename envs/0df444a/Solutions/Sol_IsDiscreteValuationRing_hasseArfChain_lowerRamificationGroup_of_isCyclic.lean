-- Prove2me | solution 1 for IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0bfd90eb-9d06-574a-8ed8-38cf3096230a

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild

import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Theorems.Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one
import Theorems.Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units
import Theorems.Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
import Theorems.Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one
import Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic

set_option autoImplicit false
namespace Ws45
namespace HATame

open IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem residue_smul_of_mem_zero {s : G} (hs : s ∈ lowerRamificationGroup R G 0) (x : R) :
    residue R (s • x) = residue R x := by
  rw [mem_lowerRamificationGroup] at hs
  have h := hs x
  rw [zero_add, pow_one] at h
  exact (Ideal.Quotient.eq).mpr h

section Core

variable [Finite G] [PerfectField (ResidueField R)]

theorem exists_invariant_sub_mem (r : R) :
    ∃ a : R, (∀ h ∈ lowerRamificationGroup R G 0, h • a = a) ∧
      r - a ∈ IsLocalRing.maximalIdeal R := by
  classical

  set H : Subgroup G := lowerRamificationGroup R G 0 with hH
  haveI : Fintype H := Fintype.ofFinite H
  let A : Subring R := FixedPoints.subring R H
  haveI : IsLocalHom (algebraMap A R) :=
    ⟨fun a h => (FixedPoints.isUnit_subring_iff a).mpr h⟩
  have halg : ∀ a : A, algebraMap (ResidueField A) (ResidueField R) (residue A a) =
      residue R (a : R) := fun a => rfl

  let q : ℕ := ringExpChar (ResidueField A)
  haveI hqA : ExpChar (ResidueField A) q := inferInstance
  haveI hqR : ExpChar (ResidueField R) q :=
    expChar_of_injective_algebraMap (algebraMap (ResidueField A) (ResidueField R)).injective q
  set N : ℕ := Fintype.card H with hN
  have hNpos : 0 < N := Fintype.card_pos

  have key : ∀ x : ResidueField R,
      x ^ q ^ N ∈ (algebraMap (ResidueField A) (ResidueField R)).range := by
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x

    have hlifts : MulSemiringAction.charpoly H r ∈ Polynomial.lifts (algebraMap A R) := by
      refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
      exact ⟨⟨(MulSemiringAction.charpoly H r).coeff n,
        fun h => MulSemiringAction.smul_coeff_charpoly r n h⟩, rfl⟩
    obtain ⟨f, hfF, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts
      (MulSemiringAction.monic_charpoly H r)

    set fb : (ResidueField A)[X] := f.map (residue A) with hfb
    have hfbm : fb.Monic := hfm.map _

    have hmapF : (MulSemiringAction.charpoly H r).map (residue R) =
        (X - C (residue R r)) ^ N := by
      rw [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      have hres : ∀ g : H, residue R ((g : G) • r) = residue R r := fun g =>
        residue_smul_of_mem_zero (R := R) (G := G) g.2 r
      simp only [Subgroup.smul_def, hres, Finset.prod_const, Finset.card_univ, hN]
    have hfbmap : fb.map (algebraMap (ResidueField A) (ResidueField R)) =
        (X - C (residue R r)) ^ N := by
      rw [hfb, Polynomial.map_map, ← hmapF, ← hfF, Polynomial.map_map]
      congr 1

    have hint : IsIntegral (ResidueField A) (residue R r) := by
      refine ⟨fb, hfbm, ?_⟩
      rw [← Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, hfbmap,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_self, zero_pow hNpos.ne']
    have hroot : Polynomial.aeval (residue R r) fb = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hfbmap, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_pow hNpos.ne']
    have hdvd : minpoly (ResidueField A) (residue R r) ∣ fb := minpoly.dvd _ _ hroot
    have hfb0 : fb ≠ 0 := hfbm.ne_zero
    have hsep1 : (minpoly (ResidueField A) (residue R r)).natSepDegree = 1 := by
      refine le_antisymm ?_ ?_
      · calc (minpoly (ResidueField A) (residue R r)).natSepDegree
            ≤ fb.natSepDegree := Polynomial.natSepDegree_le_of_dvd _ _ hdvd hfb0
          _ = (fb.map (algebraMap (ResidueField A) (ResidueField R))).natSepDegree := by
              rw [Polynomial.natSepDegree_map]
          _ = 1 := by rw [hfbmap, Polynomial.natSepDegree_X_sub_C_pow, if_neg hNpos.ne']
      · rw [Nat.one_le_iff_ne_zero, Polynomial.natSepDegree_ne_zero_iff]
        exact (minpoly.natDegree_pos hint).ne'
    obtain ⟨n, y, hny⟩ :=
      (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mp hsep1

    have hpow : residue R r ^ q ^ n = algebraMap (ResidueField A) (ResidueField R) y := by
      have h0 := minpoly.aeval (ResidueField A) (residue R r)
      rw [hny, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, sub_eq_zero] at h0
      exact h0
    have hdeg : q ^ n ≤ N := by
      have h1 : (minpoly (ResidueField A) (residue R r)).natDegree ≤ fb.natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hfb0
      rw [hny, Polynomial.natDegree_X_pow_sub_C, hfb, hfm.natDegree_map,
        ← hfm.natDegree_map (algebraMap A R), hfF,
        (MulSemiringAction.monic_charpoly H r).natDegree_map (residue R) |>.symm.trans
          (by rw [hmapF, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one])]
        at h1
      exact h1

    rcases (expChar_is_prime_or_one (ResidueField A) q) with hq | hq
    · have hn : n ≤ N := (Nat.lt_pow_self hq.one_lt).le.trans hdeg
      have : residue R r ^ q ^ N = (algebraMap (ResidueField A) (ResidueField R) y) ^ q ^ (N - n) := by
        rw [← hpow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hn]
      rw [this]
      exact pow_mem (RingHom.mem_range_self _ _) _
    · rw [hq, one_pow, pow_one]
      rw [hq, one_pow, pow_one] at hpow
      exact ⟨y, hpow.symm⟩

  set x : ResidueField R := (iterateFrobeniusEquiv (ResidueField R) q N).symm (residue R r) with hx
  have hxN : x ^ q ^ N = residue R r := by
    rw [← iterateFrobeniusEquiv_def, hx, RingEquiv.apply_symm_apply]
  obtain ⟨ybar, hy⟩ := key x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective ybar
  refine ⟨(a : R), fun h hh => a.2 ⟨h, hh⟩, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hxN, ← hy, halg]

theorem smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero
    {ϖ : R} (hϖ : Irreducible ϖ) {s : G} (hs : s ∈ lowerRamificationGroup R G 0) (x : R) :
    s • ϖ - ϖ ∣ s • x - x := by
  classical

  obtain ⟨x₀, hx₀⟩ := ENat.exists_eq_iInf (fun x : R => IsDiscreteValuationRing.addVal R (s • x - x))

  suffices hle : IsDiscreteValuationRing.addVal R (s • ϖ - ϖ) ≤
      IsDiscreteValuationRing.addVal R (s • x₀ - x₀) by
    refine IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hle.trans ?_)
    rw [hx₀]; exact iInf_le _ x

  obtain ⟨a, ha, hax⟩ := exists_invariant_sub_mem (R := R) (G := G) x₀
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hax
  obtain ⟨z, hz⟩ := hax
  have hx₀eq : x₀ = a + z * ϖ := by rw [← sub_eq_iff_eq_add', ← hz]
  have hsa : s • a = a := ha s hs
  have hdecomp : s • x₀ - x₀ = (s • ϖ - ϖ) * (s • z) + ϖ * (s • z - z) := by
    rw [hx₀eq, smul_add, smul_mul', hsa]; ring
  by_contra hlt
  push Not at hlt

  have h1 : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) <
      IsDiscreteValuationRing.addVal R ((s • ϖ - ϖ) * (s • z)) := by
    rw [IsDiscreteValuationRing.addVal_mul]
    exact lt_of_lt_of_le hlt le_self_add
  have h2 : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) <
      IsDiscreteValuationRing.addVal R (ϖ * (s • z - z)) := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    have hmin : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) ≤
        IsDiscreteValuationRing.addVal R (s • z - z) := by rw [hx₀]; exact iInf_le _ z
    have hfin : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) ≠ ⊤ := by
      intro htop; rw [htop] at hlt; exact not_top_lt hlt
    calc IsDiscreteValuationRing.addVal R (s • x₀ - x₀)
        < IsDiscreteValuationRing.addVal R (s • x₀ - x₀) + 1 := ENat.lt_add_one_iff hfin |>.mpr le_rfl
      _ = 1 + IsDiscreteValuationRing.addVal R (s • x₀ - x₀) := add_comm _ _
      _ ≤ 1 + IsDiscreteValuationRing.addVal R (s • z - z) := add_le_add le_rfl hmin
  have h12 := IsDiscreteValuationRing.addVal_add (R := R)
    (a := (s • ϖ - ϖ) * (s • z)) (b := ϖ * (s • z - z))
  rw [← hdecomp] at h12
  exact (lt_min h1 h2).not_ge h12

theorem mem_lowerRamificationGroup_iff_smul_uniformizer_sub_mem_pow
    {ϖ : R} (hϖ : Irreducible ϖ) {s : G} (hs : s ∈ lowerRamificationGroup R G 0) (i : ℕ) :
    s ∈ lowerRamificationGroup R G i ↔ s • ϖ - ϖ ∈ IsLocalRing.maximalIdeal R ^ (i + 1) := by
  refine ⟨fun h => (mem_lowerRamificationGroup.mp h) ϖ, fun h => ?_⟩
  rw [mem_lowerRamificationGroup]
  intro x
  obtain ⟨c, hc⟩ := smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero hϖ hs x
  rw [hc]
  exact Ideal.mul_mem_right _ _ h

end Core

end Ws45.HATame

namespace HasseArfCyc

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

local notation "Γ" => IsLocalRing.lowerRamificationGroup R G

theorem pow_add_eq_pow_of_mul_eq_zero {S : Type*} [CommRing S] (x c : S) (hxc : x * c = 0) (hcc : c * c = 0) :
    ∀ k : ℕ, 1 ≤ k → (x + c) ^ (k + 1) = x ^ (k + 1) := by
  have h1 : ∀ k : ℕ, x ^ (k + 1) * c = 0 := fun k => by rw [pow_succ, mul_assoc, hxc, mul_zero]
  have h2 : ∀ k : ℕ, (x + c) ^ (k + 1) * c = 0 := fun k => by
    rw [pow_succ, mul_assoc, add_mul, hxc, hcc, add_zero, mul_zero]
  have P : ∀ k : ℕ, x * (x + c) ^ k = x ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x * (x + c) ^ (k + 1) = (x * (x + c) ^ k) * (x + c) := by ring
        _ = x ^ (k + 1) * (x + c) := by rw [ih]
        _ = x ^ (k + 1) * x + x ^ (k + 1) * c := by ring
        _ = x ^ (k + 1 + 1) := by rw [h1, add_zero, ← pow_succ]
  intro k hk
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  calc (x + c) ^ (k + 1 + 1) = x * (x + c) ^ (k + 1) + (x + c) ^ (k + 1) * c := by ring
    _ = x ^ (k + 1 + 1) + 0 := by rw [P, h2]
    _ = x ^ (k + 1 + 1) := by ring

theorem smul_sub_mem_pow_of_mem_pow {ϖ : R} (hϖ : Irreducible ϖ) {s : G} {i : ℕ} (hi : 1 ≤ i)
    (hs : s ∈ Γ i) {y : R} (hy : y ∈ maximalIdeal R ^ (i + 1)) :
    s • y - y ∈ maximalIdeal R ^ (i + 2) := by
  have hs0 : s ∈ Γ 0 := lowerRamificationGroup_antitone (Nat.zero_le i) hs
  have hmax : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq

  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨b, rfl⟩ := hy
  set c := s • ϖ - ϖ with hc
  have hcmem : c ∈ maximalIdeal R ^ (i + 1) := (mem_lowerRamificationGroup.1 hs) ϖ
  have hsb : s • b - b ∈ maximalIdeal R := by
    have h := (mem_lowerRamificationGroup.1 hs0) b
    rwa [zero_add, pow_one] at h
  have hϖmem : ϖ ∈ maximalIdeal R := by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ

  have hsϖ : s • ϖ = ϖ + c := by rw [hc]; ring
  have e : s • (ϖ ^ (i + 1) * b) - ϖ ^ (i + 1) * b =
      ((ϖ + c) ^ (i + 1) - ϖ ^ (i + 1)) * (s • b) + ϖ ^ (i + 1) * (s • b - b) := by
    rw [smul_mul', smul_pow', hsϖ]; ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · apply Ideal.mul_mem_right

    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, map_add]
    have hxc : Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) ϖ * Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) c = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, show i + 2 = 1 + (i + 1) by ring, pow_add, pow_one]
      exact Ideal.mul_mem_mul hϖmem hcmem
    have hcc : Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) c * Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) c = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have := Ideal.mul_mem_mul hcmem hcmem
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
    rw [pow_add_eq_pow_of_mul_eq_zero _ _ hxc hcc i hi, sub_self]
  · rw [show i + 2 = (i + 1) + 1 by ring, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖmem _) hsb

theorem pow_smul_sub_sub_nsmul_mem {ϖ : R} (hϖ : Irreducible ϖ) {s : G} {i : ℕ} (hi : 1 ≤ i) (hs : s ∈ Γ i) :
    ∀ k : ℕ, s ^ k • ϖ - ϖ - (k : R) * (s • ϖ - ϖ) ∈ maximalIdeal R ^ (i + 2) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hy : s ^ k • ϖ - ϖ ∈ maximalIdeal R ^ (i + 1) :=
      (mem_lowerRamificationGroup.1 (Subgroup.pow_mem _ hs k)) ϖ
    have h1 := smul_sub_mem_pow_of_mem_pow hϖ hi hs hy
    have e : s ^ (k + 1) • ϖ - ϖ - ((k + 1 : ℕ) : R) * (s • ϖ - ϖ) =
        (s • (s ^ k • ϖ - ϖ) - (s ^ k • ϖ - ϖ)) + (s ^ k • ϖ - ϖ - (k : R) * (s • ϖ - ϖ)) := by
      rw [pow_succ', mul_smul, smul_sub]; push_cast; ring
    rw [e]
    exact Ideal.add_mem _ h1 ih

theorem mem_succ_of_mem_of_isUnit [Finite G] [PerfectField (ResidueField R)]
    {s : G} {i : ℕ} (hi : 1 ≤ i) (hs : s ∈ Γ i) (hunit : IsUnit ((orderOf s : ℕ) : R)) :
    s ∈ Γ (i + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs0 : s ∈ Γ 0 := lowerRamificationGroup_antitone (Nat.zero_le i) hs
  have key := pow_smul_sub_sub_nsmul_mem hϖ hi hs (orderOf s)
  rw [pow_orderOf_eq_one, one_smul, sub_self, zero_sub, neg_mem_iff] at key
  have hc : s • ϖ - ϖ ∈ maximalIdeal R ^ (i + 1 + 1) :=
    (Ideal.unit_mul_mem_iff_mem _ hunit).1 key
  exact (Ws45.HATame.mem_lowerRamificationGroup_iff_smul_uniformizer_sub_mem_pow hϖ hs0 (i + 1)).2 hc

end HasseArfCyc

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsCyclic G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨p, hchar⟩ := CharP.exists (IsLocalRing.ResidueField R)
  haveI := hchar
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  ·
    haveI : CharZero (IsLocalRing.ResidueField R) := CharP.charP_to_charZero _
    intro i hjump
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exfalso
      apply hjump
      refine le_antisymm ?_ (IsLocalRing.lowerRamificationGroup_antitone (Nat.le_succ i))
      intro s hs
      refine HasseArfCyc.mem_succ_of_mem_of_isUnit hi hs ?_

      have hn : ((orderOf s : ℕ) : R) ∉ IsLocalRing.maximalIdeal R := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, Nat.cast_eq_zero]
        exact (orderOf_pos s).ne'
      exact (IsLocalRing.notMem_maximalIdeal.1 hn)
  ·
    have hp : p.Prime := (CharP.char_is_prime_or_zero (IsLocalRing.ResidueField R) p).resolve_right hp0.ne'
    haveI : Fact p.Prime := ⟨hp⟩
    have hpR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ p

    have hG1 : IsPGroup p ↥(IsLocalRing.lowerRamificationGroup R G 1) :=
      IsLocalRing.isPGroup_lowerRamificationGroup_one hpR IsDiscreteValuationRing.iInf_maximalIdeal_pow_eq_bot

    obtain ⟨-, -, hcop'⟩ := IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units (R := R) (G := G)
    have hcop := hcop' p hp hpR

    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hcomm : ∀ s ∈ IsLocalRing.lowerRamificationGroup R G 0, ∀ t ∈ IsLocalRing.lowerRamificationGroup R G 0, Commute s t := by
      intro s _ t _
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg s)
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg t)
      exact Commute.zpow_zpow (Commute.refl g) a b
    have htame : ∀ j : ℕ, 1 ≤ j →
        IsLocalRing.lowerRamificationGroup R G j ≠ IsLocalRing.lowerRamificationGroup R G (j + 1) →
          (IsLocalRing.lowerRamificationGroup R G 1).relIndex (IsLocalRing.lowerRamificationGroup R G 0) ∣ j :=
      fun j hj hjump => IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute hcomm hj hjump

    have hwild : ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G 1, ∀ n : ℕ, 1 ≤ n → σ ^ p ^ n ≠ 1 →
        (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
          (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n] :=
      fun σ hσ n hn hσn => IsDiscreteValuationRing.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one hp hpR hσ hn hσn

    exact IsDiscreteValuationRing.hasseArfChain_of_isCyclic_of_dvd_of_modEq hp hG1 hcop htame hwild

end S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic
end P2MW
export P2MW.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic (solution)
