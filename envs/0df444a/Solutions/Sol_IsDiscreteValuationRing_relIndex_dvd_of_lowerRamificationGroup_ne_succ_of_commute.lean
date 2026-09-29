-- Prove2me | solution 1 for IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d3b0c866-a933-5be1-9a03-68a0bd4b73f8

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute

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

theorem core_fin [Finite G] [PerfectField (ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ) {s : G}
    (hs : s ∈ lowerRamificationGroup R G 0) (x : R) : s • ϖ - ϖ ∣ s • x - x :=
  smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero hϖ hs x

noncomputable def uu {ϖ : R} (hϖ : Irreducible ϖ) (σ : G) : Rˣ :=
  (exists_smul_uniformizer_eq_unit_mul_of_irreducible hϖ σ).choose

theorem uu_spec {ϖ : R} (hϖ : Irreducible ϖ) (σ : G) : σ • ϖ = (uu hϖ σ : R) * ϖ :=
  (exists_smul_uniformizer_eq_unit_mul_of_irreducible hϖ σ).choose_spec

theorem uu_one {ϖ : R} (hϖ : Irreducible ϖ) : uu hϖ (1 : G) = 1 :=
  smul_uniformizer_unit_one hϖ.ne_zero (uu_spec hϖ (1 : G))

theorem smul_sub_mem_maximalIdeal {s : G} (hs : s ∈ lowerRamificationGroup R G 0) (x : R) :
    s • x - x ∈ maximalIdeal R := by
  have h := (mem_lowerRamificationGroup.1 hs) x
  rwa [zero_add, pow_one] at h

theorem varpi_mem {ϖ : R} (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal R := by
  rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ

theorem uu_pow_sub_pow_mem {ϖ : R} (hϖ : Irreducible ϖ) {s : G} (hs : s ∈ lowerRamificationGroup R G 0) (n : ℕ) :
    (uu hϖ (s ^ n) : R) - (uu hϖ s : R) ^ n ∈ maximalIdeal R := by
  induction n with
  | zero => rw [pow_zero, pow_zero, uu_one, Units.val_one, sub_self]; exact zero_mem _
  | succ n ih =>
    have hcoc : (uu hϖ (s ^ n * s) : R) = (uu hϖ (s ^ n) : R) * ((s ^ n) • (uu hϖ s : R)) :=
      smul_uniformizer_unit_cocycle hϖ.ne_zero (uu_spec hϖ (s ^ n)) (uu_spec hϖ s) (uu_spec hϖ (s ^ n * s))
    have h1 : (s ^ n) • (uu hϖ s : R) - (uu hϖ s : R) ∈ maximalIdeal R :=
      smul_sub_mem_maximalIdeal ((lowerRamificationGroup R G 0).pow_mem hs n) _
    rw [pow_succ, hcoc]
    have hexp : (uu hϖ (s ^ n) : R) * ((s ^ n) • (uu hϖ s : R)) - (uu hϖ s : R) ^ (n + 1)
        = (uu hϖ (s ^ n) : R) * ((s ^ n) • (uu hϖ s : R) - (uu hϖ s : R))
          + ((uu hϖ (s ^ n) : R) - (uu hϖ s : R) ^ n) * (uu hϖ s : R) := by ring
    rw [hexp]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_right _ _ ih)

theorem pow_sub_one_mem_maximalIdeal_of_commute [Finite G] [PerfectField (ResidueField R)]
    {ϖ : R} (hϖ : Irreducible ϖ) {i : ℕ}
    {s τ : G} (hs : s ∈ lowerRamificationGroup R G 0)
    (hτ : τ ∈ lowerRamificationGroup R G i) (hτ' : τ ∉ lowerRamificationGroup R G (i + 1))
    (hc : Commute s τ) :
    (uu hϖ s : R) ^ i - 1 ∈ maximalIdeal R := by
  have hϖm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hu := uu_spec hϖ s
  have hv := uu_spec hϖ τ
  have hτ0 : τ ∈ lowerRamificationGroup R G 0 := lowerRamificationGroup_le_zero i hτ

  have hv1 : (uu hϖ τ : R) - 1 ∈ maximalIdeal R ^ i :=
    smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup hϖm hϖ0 hv hτ
  rw [hϖm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hv1
  obtain ⟨c, hcv⟩ := hv1
  have hcunit : c ∉ maximalIdeal R := by
    intro hcm
    apply hτ'
    refine mem_lowerRamificationGroup_of_smul_uniformizer_unit_sub_one_mem_pow (varpi_mem hϖ)
      (core_fin hϖ hτ0) hv ?_
    rw [hϖm, Ideal.mem_span_singleton] at hcm
    obtain ⟨d, rfl⟩ := hcm
    rw [hϖm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨d, by rw [← hcv]; ring⟩

  have hst : (s * τ) • ϖ = ((uu hϖ s : R) * (s • (uu hϖ τ : R))) * ϖ := by
    rw [mul_smul, hv, smul_mul', hu]; ring
  have hts : (τ * s) • ϖ = ((uu hϖ τ : R) * (τ • (uu hϖ s : R))) * ϖ := by
    rw [mul_smul, hu, smul_mul', hv]; ring
  have hcomm' : (uu hϖ s : R) * (s • (uu hϖ τ : R)) = (uu hϖ τ : R) * (τ • (uu hϖ s : R)) := by
    apply mul_right_cancel₀ hϖ0
    rw [← hst, ← hts, hc.eq]
  have h1 : τ • (uu hϖ s : R) - (uu hϖ s : R) ∈ maximalIdeal R ^ (i + 1) := (mem_lowerRamificationGroup.1 hτ) _
  have h2 : s • c - c ∈ maximalIdeal R := smul_sub_mem_maximalIdeal hs c
  have hsv : s • (uu hϖ τ : R) = 1 + (s • c) * (uu hϖ s : R) ^ i * ϖ ^ i := by
    have hveq : (uu hϖ τ : R) = 1 + c * ϖ ^ i := by rw [hcv]; ring
    rw [hveq, smul_add, smul_one, smul_mul', smul_pow', hu, mul_pow]
    ring
  have key : c * (uu hϖ s : R) * ϖ ^ i * ((uu hϖ s : R) ^ i - 1)
      = (uu hϖ τ : R) * (τ • (uu hϖ s : R) - (uu hϖ s : R)) - (s • c - c) * (uu hϖ s : R) ^ (i + 1) * ϖ ^ i := by
    rw [hsv] at hcomm'
    linear_combination hcomm' - (uu hϖ s : R) * hcv
  have hmem : c * (uu hϖ s : R) * ϖ ^ i * ((uu hϖ s : R) ^ i - 1) ∈ maximalIdeal R ^ (i + 1) := by
    rw [key]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) ?_
    rw [pow_succ']
    exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ h2) (Ideal.pow_mem_pow (varpi_mem hϖ) i)

  rw [hϖm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  have hmem' : c * ((uu hϖ s : R) * ((uu hϖ s : R) ^ i - 1)) ∈ maximalIdeal R := by
    rw [hϖm, Ideal.mem_span_singleton]
    refine ⟨d, mul_right_cancel₀ (pow_ne_zero i hϖ0) ?_⟩
    calc c * ((uu hϖ s : R) * ((uu hϖ s : R) ^ i - 1)) * ϖ ^ i
        = c * (uu hϖ s : R) * ϖ ^ i * ((uu hϖ s : R) ^ i - 1) := by ring
      _ = ϖ ^ (i + 1) * d := hd
      _ = ϖ * d * ϖ ^ i := by ring
  rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem hmem' with h | h
  · exact absurd h hcunit
  · rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h with h' | h'
    · exact absurd h' (fun hm => (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hm)) (uu hϖ s).isUnit)
    · exact h'

end Ws45.HATame

open IsLocalRing in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcomm : ∀ s ∈ IsLocalRing.lowerRamificationGroup R G 0,
      ∀ t ∈ IsLocalRing.lowerRamificationGroup R G 0, Commute s t)
    {i : ℕ} (hi : 1 ≤ i)
    (hjump : IsLocalRing.lowerRamificationGroup R G i ≠ IsLocalRing.lowerRamificationGroup R G (i + 1)) :
    (IsLocalRing.lowerRamificationGroup R G 1).relIndex (IsLocalRing.lowerRamificationGroup R G 0) ∣ i := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R

  have hle : lowerRamificationGroup R G (i + 1) ≤ lowerRamificationGroup R G i :=
    lowerRamificationGroup_antitone (Nat.le_succ i)
  obtain ⟨τ, hτ, hτ'⟩ : ∃ τ ∈ lowerRamificationGroup R G i, τ ∉ lowerRamificationGroup R G (i + 1) := by
    by_contra h
    apply hjump
    refine le_antisymm (fun x hx => ?_) hle
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  have hτ0 : τ ∈ lowerRamificationGroup R G 0 := lowerRamificationGroup_le_zero i hτ

  have hpow : ∀ s ∈ lowerRamificationGroup R G 0, (Ws45.HATame.uu hϖ s : R) ^ i - 1 ∈ maximalIdeal R :=
    fun s hs => Ws45.HATame.pow_sub_one_mem_maximalIdeal_of_commute hϖ hs hτ hτ' (hcomm s hs τ hτ0)

  obtain ⟨-, hcyc, -⟩ :=
    IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units (R := R) (G := G)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g

  have hgi : ((g0 : G) ^ i) ∈ lowerRamificationGroup R G 1 := by
    have hmod := Ws45.HATame.uu_pow_sub_pow_mem hϖ g0.2 i
    have h1 : (Ws45.HATame.uu hϖ ((g0 : G) ^ i) : R) - 1 ∈ maximalIdeal R ^ 1 := by
      rw [pow_one]
      have := Ideal.add_mem _ hmod (hpow (g0 : G) g0.2)
      rwa [sub_add_sub_cancel] at this
    exact mem_lowerRamificationGroup_of_smul_uniformizer_unit_sub_one_mem_pow (Ws45.HATame.varpi_mem hϖ)
      (Ws45.HATame.core_fin hϖ ((lowerRamificationGroup R G 0).pow_mem g0.2 i)) (Ws45.HATame.uu_spec hϖ _) h1
  have hone : (QuotientGroup.mk g0 : ↥(lowerRamificationGroup R G 0) ⧸
      (lowerRamificationGroup R G 1).subgroupOf (lowerRamificationGroup R G 0)) ^ i = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hgi
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  show Nat.card (↥(lowerRamificationGroup R G 0) ⧸
      (lowerRamificationGroup R G 1).subgroupOf (lowerRamificationGroup R G 0)) ∣ i
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hone

end S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
end P2MW
export P2MW.S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute (solution)
