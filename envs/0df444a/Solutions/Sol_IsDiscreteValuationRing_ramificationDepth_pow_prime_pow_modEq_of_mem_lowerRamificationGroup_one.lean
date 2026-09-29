-- Prove2me | solution 1 for IsDiscreteValuationRing.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2fe0918d-bd1d-558c-a104-63d5ee0d6e70

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one

set_option autoImplicit false

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "ideal_eq_span_pow_irreducible addVal_add mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd addVal_def eq_unit_mul_pow_irreducible exists_irreducible remainder addVal_uniformizer addVal_eq_top_iff addVal_mul mem_maximalIdeal_pow_iff_le_addVal iInf_maximalIdeal_pow_eq_bot addVal_smul ramificationDepth ramificationDepth_def mem_lowerRamificationGroup_iff_le_ramificationDepth ramificationDepth_eq_top_iff"
namespace CorePSol
p2m_open "IsDiscreteValuationRing"

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem exists_eq_pow_add_mul [PerfectField (ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {ϖ : R} (hϖ : Irreducible ϖ) (x : R) :
    ∃ y z : R, x = y ^ p + ϖ * z := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (ResidueField R) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
    have : residue R (p : R) = 0 := (residue_eq_zero_iff _).mpr hpR
    simpa using this
  haveI : ExpChar (ResidueField R) p := ExpChar.prime hp
  obtain ⟨ybar, hybar⟩ := surjective_frobenius (ResidueField R) p (residue R x)
  obtain ⟨y, rfl⟩ := residue_surjective ybar
  have hmem : x - y ^ p ∈ IsLocalRing.maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_pow]
    rw [frobenius_def] at hybar
    rw [hybar, sub_self]
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨y, z, by rw [mul_comm, hz]; ring⟩

theorem smul_sub_mem_sup_pow [PerfectField (ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {ϖ : R} (hϖ : Irreducible ϖ)
    {s : G} (hs : s ∈ lowerRamificationGroup R G 0) (n : ℕ) (x : R) :
    s • x - x ∈ Ideal.span {s • ϖ - ϖ} ⊔ (IsLocalRing.maximalIdeal R) ^ (n + 1) := by
  induction n generalizing x with
  | zero =>
    exact Ideal.mem_sup_right (by simpa using (mem_lowerRamificationGroup.mp hs) x)
  | succ n ih =>
    obtain ⟨y, z, rfl⟩ := exists_eq_pow_add_mul hp hpR hϖ x

    obtain ⟨j, hj, μ, hμ, hjμ⟩ := Submodule.mem_sup.mp (ih y)
    have hsy : s • y = y + μ + j := by
      have : s • y = (s • y - y) + y := by ring
      rw [this, ← hjμ]; ring
    have hsx : s • (y ^ p + ϖ * z) - (y ^ p + ϖ * z) =
        ((y + μ + j) ^ p - (y + μ) ^ p) + ((y + μ) ^ p - y ^ p) +
          ((s • ϖ - ϖ) * (s • z) + ϖ * (s • z - z)) := by
      rw [smul_add, smul_pow', smul_mul', hsy]; ring
    rw [hsx]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
    ·
      refine Ideal.mem_sup_left ?_
      have hdvd : j ∣ (y + μ + j) ^ p - (y + μ) ^ p := by
        have := sub_dvd_pow_sub_pow (y + μ + j) (y + μ) p
        rwa [add_sub_cancel_left] at this
      obtain ⟨c, hc⟩ := hdvd
      rw [hc]
      exact Ideal.mul_mem_right _ _ hj
    ·
      refine Ideal.mem_sup_right ?_
      have hμ' : y + μ ≡ y [SMOD (IsLocalRing.maximalIdeal R) ^ (n + 1)] := by
        rw [SModEq.sub_mem]; simpa using hμ
      have key := SModEq.pow_add_one hpR (Nat.succ_ne_zero n) hμ'
      rw [SModEq.sub_mem] at key
      exact key
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    ·
      obtain ⟨j', hj', μ', hμ', hjμ'⟩ := Submodule.mem_sup.mp (ih z)
      rw [← hjμ', mul_add]
      refine Submodule.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hj')) (Ideal.mem_sup_right ?_)
      rw [pow_succ']
      exact Ideal.mul_mem_mul (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ) hμ'

end IsDiscreteValuationRing.CorePSol

namespace IsDiscreteValuationRing p2m_export "IsDiscreteValuationRing" "ideal_eq_span_pow_irreducible addVal_add mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd addVal_def eq_unit_mul_pow_irreducible exists_irreducible remainder addVal_uniformizer addVal_eq_top_iff addVal_mul mem_maximalIdeal_pow_iff_le_addVal iInf_maximalIdeal_pow_eq_bot addVal_smul ramificationDepth ramificationDepth_def mem_lowerRamificationGroup_iff_le_ramificationDepth ramificationDepth_eq_top_iff" end IsDiscreteValuationRing
p2m_open_scoped "IsDiscreteValuationRing" in
open IsDiscreteValuationRing.CorePSol IsLocalRing in
theorem IsDiscreteValuationRing.smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero_of_prime_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {ϖ : R} (hϖ : Irreducible ϖ) {s : G} (hs : s ∈ IsLocalRing.lowerRamificationGroup R G 0)
    (x : R) :
    s • ϖ - ϖ ∣ s • x - x := by

  by_cases h0 : s • ϖ - ϖ = 0
  ·
    rw [h0, zero_dvd_iff]
    have hall : ∀ n : ℕ, s • x - x ∈ (IsLocalRing.maximalIdeal R) ^ n := by
      intro n
      have := smul_sub_mem_sup_pow hp hpR hϖ hs n x
      rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq] at this
      exact Ideal.pow_le_pow_right (Nat.le_succ n) this
    have hmem : s • x - x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n := Ideal.mem_iInf.mpr hall
    rwa [IsDiscreteValuationRing.iInf_maximalIdeal_pow_eq_bot, Ideal.mem_bot] at hmem
  · obtain ⟨d, hd⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      ((Ideal.span_singleton_eq_bot.not).mpr h0) hϖ
    have hJ : Ideal.span {s • ϖ - ϖ} = (IsLocalRing.maximalIdeal R) ^ d := by
      rw [hd, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    have := smul_sub_mem_sup_pow hp hpR hϖ hs d x
    rw [hJ, sup_eq_left.mpr (Ideal.pow_le_pow_right (Nat.le_succ d)), ← hJ] at this
    exact Ideal.mem_span_singleton.mp this

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "ideal_eq_span_pow_irreducible addVal_add mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd addVal_def eq_unit_mul_pow_irreducible exists_irreducible remainder addVal_uniformizer addVal_eq_top_iff addVal_mul mem_maximalIdeal_pow_iff_le_addVal iInf_maximalIdeal_pow_eq_bot addVal_smul ramificationDepth ramificationDepth_def mem_lowerRamificationGroup_iff_le_ramificationDepth ramificationDepth_eq_top_iff"
namespace Sen1Sol
p2m_open "IsDiscreteValuationRing"

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem ramificationDepth_eq_addVal [PerfectField (ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {π : R} (hπ : Irreducible π)
    {s : G} (hs : s ∈ lowerRamificationGroup R G 0) :
    ramificationDepth R G s = addVal R (s • π - π) := by
  rw [ramificationDepth_def]
  refine le_antisymm (iInf_le _ π) (le_iInf fun x => ?_)
  exact addVal_le_iff_dvd.mpr
    (IsDiscreteValuationRing.smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero_of_prime_mem
      hp hpR hπ hs x)

theorem isUnit_natCast_of_not_dvd {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {i : ℕ} (hi : ¬ p ∣ i) : IsUnit (i : R) := by
  haveI : CharP (ResidueField R) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
    have : residue R (p : R) = 0 := (residue_eq_zero_iff _).mpr hpR
    simpa using this
  by_contra hunit
  have hmem : (i : R) ∈ IsLocalRing.maximalIdeal R := hunit
  have : residue R (i : R) = 0 := (residue_eq_zero_iff _).mpr hmem
  rw [map_natCast, CharP.cast_eq_zero_iff (ResidueField R) p] at this
  exact hi this

end IsDiscreteValuationRing.Sen1Sol

p2m_open_scoped "IsDiscreteValuationRing" in
open IsDiscreteValuationRing.Sen1Sol IsLocalRing _root_.IsDiscreteValuationRing _root_.P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.IsDiscreteValuationRing in
theorem IsDiscreteValuationRing.ramificationDepth_pow_eq_of_mem_lowerRamificationGroup_one_of_not_dvd
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {σ : G} (hσ : σ ∈ IsLocalRing.lowerRamificationGroup R G 1) {i : ℕ} (hi : ¬ p ∣ i) :
    IsDiscreteValuationRing.ramificationDepth R G (σ ^ i) =
      IsDiscreteValuationRing.ramificationDepth R G σ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hσ0 : σ ∈ lowerRamificationGroup R G 0 := lowerRamificationGroup_antitone (Nat.zero_le 1) hσ
  have hσi0 : σ ^ i ∈ lowerRamificationGroup R G 0 := Subgroup.pow_mem _ hσ0 i

  have hc : ∀ t : ℕ, ∃ c : R, σ ^ t • ϖ = ϖ + ϖ ^ 2 * c := by
    intro t
    have h := (mem_lowerRamificationGroup.mp (Subgroup.pow_mem _ hσ t)) ϖ
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [mul_comm] at hc; linear_combination -hc⟩
  choose c hc using hc

  have hsum : (∑ t ∈ Finset.range i, σ ^ t • ϖ) = ϖ * ((i : R) + ϖ * ∑ t ∈ Finset.range i, c t) := by
    calc (∑ t ∈ Finset.range i, σ ^ t • ϖ) = ∑ t ∈ Finset.range i, (ϖ + ϖ ^ 2 * c t) :=
          Finset.sum_congr rfl fun t _ => hc t
      _ = (∑ t ∈ Finset.range i, ϖ) + ∑ t ∈ Finset.range i, ϖ ^ 2 * c t := Finset.sum_add_distrib
      _ = (i : R) * ϖ + ϖ ^ 2 * ∑ t ∈ Finset.range i, c t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
      _ = ϖ * ((i : R) + ϖ * ∑ t ∈ Finset.range i, c t) := by ring
  have hu : IsUnit ((i : R) + ϖ * ∑ t ∈ Finset.range i, c t) := by

    have hi' := isUnit_natCast_of_not_dvd (R := R) hp hpR hi
    have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal R := by
      rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
    have hm : ϖ * ∑ t ∈ Finset.range i, c t ∈ IsLocalRing.maximalIdeal R :=
      Ideal.mul_mem_right _ _ hϖmem
    by_contra hnu
    have hmem : (i : R) + ϖ * ∑ t ∈ Finset.range i, c t ∈ IsLocalRing.maximalIdeal R := hnu
    have : (i : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hmem hm
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hi'
  have hϖ' : Irreducible (∑ t ∈ Finset.range i, σ ^ t • ϖ) := by
    rw [hsum]
    exact (irreducible_mul_isUnit hu).mpr hϖ

  have htel : σ • (∑ t ∈ Finset.range i, σ ^ t • ϖ) - ∑ t ∈ Finset.range i, σ ^ t • ϖ = σ ^ i • ϖ - ϖ := by
    rw [Finset.smul_sum]
    have h1 : ∀ t ∈ Finset.range i, σ • (σ ^ t • ϖ) = σ ^ (t + 1) • ϖ := fun t _ => by
      rw [smul_smul, ← pow_succ']
    rw [Finset.sum_congr rfl h1]
    have h2 := Finset.sum_range_succ (fun t => σ ^ t • ϖ) i
    have h3 := Finset.sum_range_succ' (fun t => σ ^ t • ϖ) i
    simp only [pow_zero, one_smul] at h3
    linear_combination h2 - h3

  rw [ramificationDepth_eq_addVal hp hpR hϖ hσi0, ramificationDepth_eq_addVal hp hpR hϖ' hσ0, htel]

p2m_open_scoped "IsDiscreteValuationRing" in
theorem IsDiscreteValuationRing.exists_sub_mem_maximalIdeal_and_smul_sub_mem_pow_of_prime_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {s : G} (hs : s ∈ IsLocalRing.lowerRamificationGroup R G 0) (u : R) (M : ℕ) :
    ∃ θ : R, θ - u ∈ IsLocalRing.maximalIdeal R ∧
      s • θ - θ ∈ (IsLocalRing.maximalIdeal R) ^ (M + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩

  have hp0 : (p : IsLocalRing.ResidueField R) = 0 := by
    have h := (IsLocalRing.residue_eq_zero_iff (p : R)).mpr hpR
    rwa [map_natCast] at h
  haveI : CharP (IsLocalRing.ResidueField R) p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
  haveI : ExpChar (IsLocalRing.ResidueField R) p := ExpChar.prime hp

  obtain ⟨wbar, hwbar⟩ := (bijective_iterateFrobenius (IsLocalRing.ResidueField R) p M).2 (IsLocalRing.residue R u)
  obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective wbar
  refine ⟨w ^ p ^ M, ?_, ?_⟩
  ·
    have h : IsLocalRing.residue R (w ^ p ^ M) = IsLocalRing.residue R u := by
      rw [map_pow, ← hwbar, iterateFrobenius_def]
    exact Ideal.Quotient.eq.mp h
  ·
    have hsw : s • w ≡ w [SMOD IsLocalRing.maximalIdeal R] := by
      rw [SModEq.sub_mem]
      have h := (IsLocalRing.mem_lowerRamificationGroup.mp hs) w
      rwa [zero_add, pow_one] at h
    have key := SModEq.pow_pow_add_one hpR hsw M
    rw [SModEq.sub_mem] at key
    rw [smul_pow']
    exact key

namespace Ws45
namespace Sen2

p2m_open "IsDiscreteValuationRing P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.IsDiscreteValuationRing"

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem addVal_prod_smul_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) (ρ : G) (s : Finset ℕ) (f : ℕ → ℕ) :
    addVal R (∏ t ∈ s, ρ ^ (f t) • ϖ) = (s.card : ℕ∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, addVal_mul, ih, addVal_smul, addVal_uniformizer hϖ, Finset.card_insert_of_notMem ha]
    push_cast
    ring

theorem addVal_prod_pow_smul_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) (ρ : G) (s : Finset ℕ) :
    addVal R (∏ t ∈ s, ρ ^ t • ϖ) = (s.card : ℕ∞) := by
  simpa using addVal_prod_smul_uniformizer hϖ ρ s id

end Ws45.Sen2

p2m_open_scoped "IsDiscreteValuationRing" in
open _root_.IsDiscreteValuationRing _root_.P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.IsDiscreteValuationRing in
theorem IsDiscreteValuationRing.exists_addVal_eq_and_addVal_smul_sub_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    {ϖ : R} (hϖ : Irreducible ϖ) (ρ : G) {k : ℕ} (hk : 1 ≤ k) :
    ∃ α : R, IsDiscreteValuationRing.addVal R α = k ∧
      IsDiscreteValuationRing.addVal R (ρ • α - α) =
        ((k - 1 : ℕ) : ℕ∞) + IsDiscreteValuationRing.addVal R (ρ ^ k • ϖ - ϖ) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨∏ t ∈ Finset.range (m + 1), ρ ^ t • ϖ, ?_, ?_⟩
  · rw [Ws45.Sen2.addVal_prod_pow_smul_uniformizer hϖ ρ, Finset.card_range]
  ·
    have hρ : ρ • (∏ t ∈ Finset.range (m + 1), ρ ^ t • ϖ) = ∏ t ∈ Finset.range (m + 1), ρ ^ (t + 1) • ϖ := by
      rw [Finset.smul_prod']
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [smul_smul, pow_succ']
    have hsplit : ρ • (∏ t ∈ Finset.range (m + 1), ρ ^ t • ϖ) - ∏ t ∈ Finset.range (m + 1), ρ ^ t • ϖ
        = (∏ t ∈ Finset.range m, ρ ^ (t + 1) • ϖ) * (ρ ^ (m + 1) • ϖ - ϖ) := by
      rw [hρ, Finset.prod_range_succ, Finset.prod_range_succ' (fun t => ρ ^ t • ϖ), pow_zero, one_smul]
      ring
    rw [hsplit, addVal_mul, Ws45.Sen2.addVal_prod_smul_uniformizer hϖ ρ _ (fun t => t + 1), Finset.card_range,
      Nat.add_sub_cancel]

namespace Ws45
namespace Digits

p2m_open "IsDiscreteValuationRing P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.IsDiscreteValuationRing"

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem exists_unit_mul_pow_of_addVal_eq {ϖ : R} (hϖ : Irreducible ϖ) {x : R} {n : ℕ}
    (hx : addVal R x = n) : ∃ g : Rˣ, x = (g : R) * ϖ ^ n := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, (addVal_eq_top_iff).2 rfl] at hx; exact ENat.top_ne_coe n hx
  obtain ⟨m, g, hxm⟩ := eq_unit_mul_pow_irreducible hx0 hϖ
  have hm : addVal R x = m := addVal_def x g hϖ m hxm
  rw [hx] at hm
  have : n = m := by exact_mod_cast hm
  subst this
  exact ⟨g, hxm⟩

theorem exists_digit [PerfectField (IsLocalRing.ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {s : G} (hs : s ∈ IsLocalRing.lowerRamificationGroup R G 0)
    {ϖ : R} (hϖ : Irreducible ϖ) {n : ℕ} {γ : R} (hγ : addVal R γ = n) (M : ℕ)
    {β : R} (hβ : β ∈ IsLocalRing.maximalIdeal R ^ n) :
    ∃ t : R, (t = 0 ∨ IsUnit t) ∧ s • t - t ∈ IsLocalRing.maximalIdeal R ^ (M + 1) ∧ β - t * γ ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
  have hϖm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨g, hg⟩ := exists_unit_mul_pow_of_addVal_eq hϖ hγ
  rw [hϖm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hβ
  obtain ⟨b, hb⟩ := hβ
  by_cases hbm : b ∈ IsLocalRing.maximalIdeal R
  · refine ⟨0, Or.inl rfl, by rw [smul_zero, sub_self]; exact zero_mem _, ?_⟩
    rw [zero_mul, sub_zero, ← hb, pow_succ']
    exact Ideal.mul_mem_mul hbm (Ideal.pow_mem_pow (by rw [hϖm]; exact Ideal.mem_span_singleton_self ϖ) n)
  · have hbu : IsUnit b := by
      by_contra h; exact hbm ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
    obtain ⟨θ, hθu, hθs⟩ :=
      IsDiscreteValuationRing.exists_sub_mem_maximalIdeal_and_smul_sub_mem_pow_of_prime_mem hp hpR hs
        (b * ((g⁻¹ : Rˣ) : R)) M
    have hθunit : IsUnit θ := by
      by_contra h
      have hθm : θ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
      have : b * ((g⁻¹ : Rˣ) : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ hθm hθu
        rwa [sub_sub_cancel] at this
      exact hbm (by simpa using Ideal.mul_mem_right (g : R) _ this)
    refine ⟨θ, Or.inr hθunit, hθs, ?_⟩
    have hexp : β - θ * γ = -((θ - b * ((g⁻¹ : Rˣ) : R)) * (g : R)) * ϖ ^ n := by
      rw [← hb, hg]
      have : (b * ((g⁻¹ : Rˣ) : R)) * (g : R) = b := by rw [mul_assoc, Units.inv_mul, mul_one]
      linear_combination (-(ϖ ^ n)) * this
    rw [hexp, pow_succ']
    exact Ideal.mul_mem_mul (neg_mem (Ideal.mul_mem_right _ _ hθu))
      (Ideal.pow_mem_pow (by rw [hϖm]; exact Ideal.mem_span_singleton_self ϖ) n)

theorem exists_digits_Ico [PerfectField (IsLocalRing.ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {s : G} (hs : s ∈ IsLocalRing.lowerRamificationGroup R G 0)
    (γ : ℕ → R) (hγ : ∀ k : ℕ, addVal R (γ k) = k) (a : ℕ) (M : ℕ) {β : R} (hβ : β ∈ IsLocalRing.maximalIdeal R ^ a)
    (N : ℕ) (haN : a ≤ N) :
    ∃ θ : ℕ → R, (∀ k : ℕ, θ k = 0 ∨ IsUnit (θ k)) ∧
      (∀ k : ℕ, s • θ k - θ k ∈ IsLocalRing.maximalIdeal R ^ (M + 1)) ∧
      β - ∑ k ∈ Finset.Ico a N, θ k * γ k ∈ IsLocalRing.maximalIdeal R ^ N := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  induction N, haN using Nat.le_induction with
  | base =>
    refine ⟨fun _ => 0, fun _ => Or.inl rfl, fun _ => by rw [smul_zero, sub_self]; exact zero_mem _, ?_⟩
    rw [Finset.Ico_self, Finset.sum_empty, sub_zero]
    exact hβ
  | succ N hN ih =>
    obtain ⟨θ, hθ0, hθs, hrem⟩ := ih
    obtain ⟨t, ht0, hts, ht⟩ := exists_digit hp hpR hs hϖ (hγ N) M hrem
    classical
    refine ⟨Function.update θ N t, fun k => ?_, fun k => ?_, ?_⟩
    · rcases eq_or_ne k N with rfl | hk
      · rw [Function.update_self]; exact ht0
      · rw [Function.update_of_ne hk]; exact hθ0 k
    · rcases eq_or_ne k N with rfl | hk
      · rw [Function.update_self]; exact hts
      · rw [Function.update_of_ne hk]; exact hθs k
    · rw [Finset.sum_Ico_succ_top hN, Function.update_self]
      have hsum : ∑ k ∈ Finset.Ico a N, Function.update θ N t k * γ k = ∑ k ∈ Finset.Ico a N, θ k * γ k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (Finset.mem_Ico.1 hk).2.ne]
      rw [hsum, ← sub_sub]
      exact ht

end Ws45.Digits

p2m_open_scoped "IsDiscreteValuationRing" in
theorem IsDiscreteValuationRing.exists_digits_sub_sum_mem_pow_of_prime_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {s : G} (hs : s ∈ IsLocalRing.lowerRamificationGroup R G 0)
    (γ : ℕ → R) (hγ : ∀ k : ℕ, IsDiscreteValuationRing.addVal R (γ k) = k)
    {a N : ℕ} (haN : a ≤ N) (M : ℕ) {β : R} (hβ : β ∈ (IsLocalRing.maximalIdeal R) ^ a) :
    ∃ θ : ℕ → R, (∀ k : ℕ, θ k = 0 ∨ IsUnit (θ k)) ∧
      (∀ k : ℕ, s • θ k - θ k ∈ (IsLocalRing.maximalIdeal R) ^ (M + 1)) ∧
      β - ∑ k ∈ Finset.Icc a N, θ k * γ k ∈ (IsLocalRing.maximalIdeal R) ^ (N + 1) := by
  obtain ⟨θ, h0, hsm, hrem⟩ :=
    Ws45.Digits.exists_digits_Ico hp hpR hs γ hγ a M hβ (N + 1) (Nat.le_succ_of_le haN)
  refine ⟨θ, h0, hsm, ?_⟩
  rw [← Finset.Ico_succ_right_eq_Icc]
  exact hrem

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "ideal_eq_span_pow_irreducible addVal_add mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd addVal_def eq_unit_mul_pow_irreducible exists_irreducible remainder addVal_uniformizer addVal_eq_top_iff addVal_mul mem_maximalIdeal_pow_iff_le_addVal iInf_maximalIdeal_pow_eq_bot addVal_smul ramificationDepth ramificationDepth_def mem_lowerRamificationGroup_iff_le_ramificationDepth ramificationDepth_eq_top_iff"
namespace Sen3Sol
p2m_open "IsDiscreteValuationRing"

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem smul_sub_mem_pow_add {s : G} {i : ℕ} (hs : s ∈ lowerRamificationGroup R G i)
    (a : ℕ) {x : R} (hx : x ∈ (IsLocalRing.maximalIdeal R) ^ a) :
    s • x - x ∈ (IsLocalRing.maximalIdeal R) ^ (a + i) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  have hsϖ : s • ϖ - ϖ ∈ (IsLocalRing.maximalIdeal R) ^ (i + 1) := (mem_lowerRamificationGroup.mp hs) ϖ
  induction a generalizing x with
  | zero =>
    exact Ideal.pow_le_pow_right (by omega) ((mem_lowerRamificationGroup.mp hs) x)
  | succ a ih =>

    have hx' : x ∈ Ideal.span {ϖ ^ (a + 1)} := by
      rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
    have hy : z * ϖ ^ a ∈ (IsLocalRing.maximalIdeal R) ^ a := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton'.mpr ⟨z, rfl⟩
    have hsy : s • (z * ϖ ^ a) ∈ (IsLocalRing.maximalIdeal R) ^ a :=
      IsLocalRing.smul_mem_maximalIdeal_pow_iff.mpr hy
    have hdecomp : s • (z * ϖ ^ (a + 1)) - z * ϖ ^ (a + 1) =
        (s • ϖ - ϖ) * (s • (z * ϖ ^ a)) + ϖ * (s • (z * ϖ ^ a) - z * ϖ ^ a) := by
      rw [pow_succ, ← mul_assoc, smul_mul', smul_mul']
      ring
    rw [hdecomp]
    refine Submodule.add_mem _ ?_ ?_
    · have := Ideal.mul_mem_mul hsϖ hsy
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
    · have := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self ϖ |> fun h => (hϖ.maximalIdeal_eq ▸ h :
        ϖ ∈ IsLocalRing.maximalIdeal R)) (ih hy)
      rw [← pow_succ'] at this
      exact Ideal.pow_le_pow_right (by omega) this

theorem addVal_add_eq_of_lt {x y : R} (h : addVal R x < addVal R y) : addVal R (x + y) = addVal R x := by
  refine le_antisymm ?_ ?_
  · by_contra hlt
    push Not at hlt
    have h1 : min (addVal R (x + y)) (addVal R (-y)) ≤ addVal R (x + y + -y) := addVal_add
    rw [add_neg_cancel_right, AddValuation.map_neg] at h1
    have : addVal R x < min (addVal R (x + y)) (addVal R y) := lt_min hlt h
    exact absurd (this.trans_le h1) (lt_irrefl _)
  · calc addVal R x = min (addVal R x) (addVal R y) := (min_eq_left h.le).symm
      _ ≤ addVal R (x + y) := addVal_add

theorem smul_sum_range_sub (σ : G) (α : R) (m : ℕ) :
    σ • (∑ t ∈ Finset.range m, σ ^ t • α) - ∑ t ∈ Finset.range m, σ ^ t • α = σ ^ m • α - α := by
  rw [Finset.smul_sum]
  have h1 : ∀ t ∈ Finset.range m, σ • (σ ^ t • α) = σ ^ (t + 1) • α := fun t _ => by
    rw [smul_smul, ← pow_succ']
  rw [Finset.sum_congr rfl h1]
  have h2 := Finset.sum_range_succ (fun t => σ ^ t • α) m
  have h3 := Finset.sum_range_succ' (fun t => σ ^ t • α) m
  simp only [pow_zero, one_smul] at h3
  linear_combination h2 - h3

theorem sum_range_smul_mem_pow_succ {p : ℕ} (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {σ : G} (hσ : σ ∈ lowerRamificationGroup R G 1) {a : ℕ} {α : R}
    (hα : α ∈ (IsLocalRing.maximalIdeal R) ^ a) :
    (∑ t ∈ Finset.range p, σ ^ t • α) ∈ (IsLocalRing.maximalIdeal R) ^ (a + 1) := by
  have hrw : (∑ t ∈ Finset.range p, σ ^ t • α) = (p : R) * α + ∑ t ∈ Finset.range p, (σ ^ t • α - α) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [hrw]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun t _ => ?_)
  · rw [pow_succ']
    exact Ideal.mul_mem_mul hpR hα
  · exact smul_sub_mem_pow_add (Subgroup.pow_mem _ hσ t) a hα

variable [FaithfulSMul G R]

theorem coe_toNat_ramificationDepth {τ : G} (hτ : τ ≠ 1) :
    ((ramificationDepth R G τ).toNat : ℕ∞) = ramificationDepth R G τ :=
  ENat.coe_toNat ((ramificationDepth_eq_top_iff (R := R)).not.mpr hτ)

theorem mem_iff_succ_le_toNat {τ : G} (hτ : τ ≠ 1) (j : ℕ) :
    τ ∈ lowerRamificationGroup R G j ↔ j + 1 ≤ (ramificationDepth R G τ).toNat := by
  rw [mem_lowerRamificationGroup_iff_le_ramificationDepth, ← coe_toNat_ramificationDepth hτ]
  norm_cast

end IsDiscreteValuationRing.Sen3Sol

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "ideal_eq_span_pow_irreducible addVal_add mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd addVal_def eq_unit_mul_pow_irreducible exists_irreducible remainder addVal_uniformizer addVal_eq_top_iff addVal_mul mem_maximalIdeal_pow_iff_le_addVal iInf_maximalIdeal_pow_eq_bot addVal_smul ramificationDepth ramificationDepth_def mem_lowerRamificationGroup_iff_le_ramificationDepth ramificationDepth_eq_top_iff"
namespace Sen3Sol
p2m_open "IsDiscreteValuationRing"

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem depth_eq_addVal [PerfectField (ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {π : R} (hπ : Irreducible π)
    {s : G} (hs : s ∈ lowerRamificationGroup R G 0) :
    ramificationDepth R G s = addVal R (s • π - π) := by
  rw [ramificationDepth_def]
  refine le_antisymm (iInf_le _ π) (le_iInf fun x => ?_)
  exact addVal_le_iff_dvd.mpr
    (IsDiscreteValuationRing.smul_sub_dvd_smul_sub_of_mem_lowerRamificationGroup_zero_of_prime_mem
      hp hpR hπ hs x)

theorem depth_pow_eq [PerfectField (ResidueField R)]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {σ : G} (hσ : σ ∈ lowerRamificationGroup R G 1) {k : ℕ} (hk : k ≠ 0) :
    ramificationDepth R G (σ ^ k) = ramificationDepth R G (σ ^ p ^ (padicValNat p k)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdecomp : p ^ (padicValNat p k) * (k / p ^ (padicValNat p k)) = k := by
    rw [← Nat.factorization_def k hp]
    exact Nat.ordProj_mul_ordCompl_eq_self k p
  have hndvd : ¬ p ∣ k / p ^ (padicValNat p k) := by
    rw [← Nat.factorization_def k hp]
    exact Nat.not_dvd_ordCompl hp hk
  conv_lhs => rw [← hdecomp, pow_mul]
  exact IsDiscreteValuationRing.ramificationDepth_pow_eq_of_mem_lowerRamificationGroup_one_of_not_dvd
    hp hpR (Subgroup.pow_mem _ hσ _) hndvd

end IsDiscreteValuationRing.Sen3Sol

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "ideal_eq_span_pow_irreducible addVal_add mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd addVal_def eq_unit_mul_pow_irreducible exists_irreducible remainder addVal_uniformizer addVal_eq_top_iff addVal_mul mem_maximalIdeal_pow_iff_le_addVal iInf_maximalIdeal_pow_eq_bot addVal_smul ramificationDepth ramificationDepth_def mem_lowerRamificationGroup_iff_le_ramificationDepth ramificationDepth_eq_top_iff"
namespace Sen3Sol
p2m_open "IsDiscreteValuationRing"

theorem exists_min_addVal_sum_eq {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (S : Finset ℕ) (hS : S.Nonempty) (f : ℕ → R) (w : ℕ → ℕ)
    (hf : ∀ k ∈ S, IsDiscreteValuationRing.addVal R (f k) = w k) (hw : Set.InjOn w S) :
    ∃ k₀ ∈ S, (∀ k ∈ S, w k₀ ≤ w k) ∧ IsDiscreteValuationRing.addVal R (∑ k ∈ S, f k) = w k₀ := by
  classical
  obtain ⟨k₀, hk₀, hmin⟩ := S.exists_min_image w hS
  refine ⟨k₀, hk₀, hmin, ?_⟩
  have hlt : IsDiscreteValuationRing.addVal R (f k₀) <
      IsDiscreteValuationRing.addVal R (∑ k ∈ S \ {k₀}, f k) := by
    rw [hf k₀ hk₀]
    refine AddValuation.map_lt_sum _ (ENat.coe_ne_top _) fun k hk => ?_
    have hkS : k ∈ S := (Finset.mem_sdiff.1 hk).1
    have hne : k ≠ k₀ := fun h => (Finset.mem_sdiff.1 hk).2 (Finset.mem_singleton.2 h)
    rw [hf k hkS]
    exact_mod_cast lt_of_le_of_ne (hmin k hkS) (fun h => hne (hw hkS hk₀ h.symm))
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hk₀, AddValuation.map_add_eq_of_lt_left _ hlt, hf k₀ hk₀]

theorem eq_of_w_eq {p n : ℕ} (hp : p.Prime) (e : ℕ → ℕ)
    (hmono : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ n → e j₁ ≤ e j₂)
    (hchain : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ + 1 ≤ n → p ^ (j₁ + 1) ∣ e j₂ - e j₁)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (hk₁n : ¬ p ^ n ∣ k₁) (hk₂n : ¬ p ^ n ∣ k₂)
    (h : k₁ - 1 + e (padicValNat p k₁) = k₂ - 1 + e (padicValNat p k₂)) : k₁ = k₂ := by
  haveI := Fact.mk hp
  set j₁ := padicValNat p k₁ with hj₁
  set j₂ := padicValNat p k₂ with hj₂
  have hj₁n : j₁ + 1 ≤ n := by
    by_contra hlt
    exact hk₁n ((padicValNat_dvd_iff_le hk₁).2 (by omega))
  have hj₂n : j₂ + 1 ≤ n := by
    by_contra hlt
    exact hk₂n ((padicValNat_dvd_iff_le hk₂).2 (by omega))
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · exfalso
    have hle := hmono j₁ j₂ hlt.le (by omega)
    have hd := hchain j₁ j₂ hlt.le hj₂n
    have hk2 : p ^ (j₁ + 1) ∣ k₂ := (padicValNat_dvd_iff_le hk₂).2 (by omega)
    have hk1 : p ^ (j₁ + 1) ∣ k₁ := by
      have : k₁ = k₂ + (e j₂ - e j₁) := by omega
      rw [this]; exact dvd_add hk2 hd
    have := (padicValNat_dvd_iff_le hk₁).1 hk1
    omega
  · rw [heq] at h; omega
  · exfalso
    have hle := hmono j₂ j₁ hgt.le (by omega)
    have hd := hchain j₂ j₁ hgt.le hj₁n
    have hk1 : p ^ (j₂ + 1) ∣ k₁ := (padicValNat_dvd_iff_le hk₁).2 (by omega)
    have hk2 : p ^ (j₂ + 1) ∣ k₂ := by
      have : k₂ = k₁ + (e j₁ - e j₂) := by omega
      rw [this]; exact dvd_add hk1 hd
    have := (padicValNat_dvd_iff_le hk₂).1 hk2
    omega

theorem w_ne_V {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (e : ℕ → ℕ)
    (hmono : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ n → e j₁ ≤ e j₂)
    (hchain : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ + 1 ≤ n → p ^ (j₁ + 1) ∣ e j₂ - e j₁)
    (hDprev : p ^ (n - 1) ∣ e n - e (n - 1)) (hDn : ¬ p ^ n ∣ e n - e (n - 1))
    {k : ℕ} (hk : (p - 1) * (e n - e (n - 1)) + 1 ≤ k) (hkn : ¬ p ^ n ∣ k) :
    k - 1 + e (padicValNat p k) ≠ (p - 1) * (e n - e (n - 1)) - 1 + e n := by
  haveI := Fact.mk hp
  intro h
  set D := e n - e (n - 1) with hD
  set a := (p - 1) * D with ha
  set j := padicValNat p k with hj
  have hk0 : k ≠ 0 := by omega
  have hjn : j + 1 ≤ n := by
    by_contra hlt
    exact hkn ((padicValNat_dvd_iff_le hk0).2 (by omega))
  have hD0 : D ≠ 0 := fun h0 => hDn (by rw [h0]; exact dvd_zero _)
  have hp2 := hp.two_le
  have ha1 : D ≤ a := by
    rw [ha]; exact Nat.le_mul_of_pos_left D (by omega)
  have hmono1 : e (n - 1) ≤ e n := hmono _ _ (Nat.sub_le n 1) le_rfl
  have hmonoj : e j ≤ e (n - 1) := hmono _ _ (by omega) (Nat.sub_le n 1)
  rcases eq_or_lt_of_le (show j ≤ n - 1 by omega) with hjeq | hjlt
  ·
    have hpD : a + D = p * D := by
      rw [ha, Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left D (by omega))]
    have hk' : k = p * D := by
      rw [hjeq] at h
      omega
    apply hkn
    rw [hk']
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ']
    refine mul_dvd_mul_left p ?_
    simpa using hDprev
  · have hd1 : p ^ (j + 1) ∣ e (n - 1) - e j := hchain j (n - 1) hjlt.le (by omega)
    have hd2 : p ^ (j + 1) ∣ D := (pow_dvd_pow p (by omega : j + 1 ≤ n - 1)).trans hDprev
    have hd3 : p ^ (j + 1) ∣ a := by rw [ha]; exact dvd_mul_of_dvd_right hd2 _
    have hk' : k = a + (D + (e (n - 1) - e j)) := by omega
    have hkd : p ^ (j + 1) ∣ k := by rw [hk']; exact dvd_add hd3 (dvd_add hd2 hd1)
    have := (padicValNat_dvd_iff_le hk0).1 hkd
    omega

end IsDiscreteValuationRing.Sen3Sol

open IsDiscreteValuationRing.Sen3Sol IsLocalRing _root_.IsDiscreteValuationRing _root_.P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.IsDiscreteValuationRing in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    [PerfectField (IsLocalRing.ResidueField R)]
    {σ : G} (hσ : σ ∈ IsLocalRing.lowerRamificationGroup R G 1)
    {n : ℕ} (hn : 1 ≤ n) (hσn : σ ^ p ^ n ≠ 1) :
    (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
      (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R

  induction n using Nat.strong_induction_on generalizing σ with
  | _ n ih =>

  set e : ℕ → ℕ := fun j => (ramificationDepth R G (σ ^ p ^ j)).toNat with he

  have hne : ∀ j, j ≤ n → σ ^ p ^ j ≠ 1 := by
    intro j hj h1
    apply hσn
    rw [← Nat.add_sub_cancel' hj, pow_add, pow_mul, h1, one_pow]
  have hmem1 : ∀ j, σ ^ p ^ j ∈ lowerRamificationGroup R G 1 := fun j => Subgroup.pow_mem _ hσ _
  have hmem0 : ∀ k, σ ^ k ∈ lowerRamificationGroup R G 0 :=
    fun k => Subgroup.pow_mem _ (lowerRamificationGroup_antitone (Nat.zero_le 1) hσ) _

  have htwo : ∀ j, j ≤ n → 2 ≤ e j := fun j hj =>
    (mem_iff_succ_le_toNat (hne j hj) 1).mp (hmem1 j)
  have hmono : ∀ j, j + 1 ≤ n → e j ≤ e (j + 1) := by
    intro j hj
    have h2j := htwo j (by omega)
    have hmemej : σ ^ p ^ j ∈ lowerRamificationGroup R G (e j - 1) := by
      rw [mem_iff_succ_le_toNat (hne j (by omega))]
      change e j - 1 + 1 ≤ e j
      omega
    have h1 : σ ^ p ^ (j + 1) ∈ lowerRamificationGroup R G (e j - 1) := by
      rw [pow_succ, pow_mul]
      exact Subgroup.pow_mem _ hmemej p
    have := (mem_iff_succ_le_toNat (hne (j + 1) hj) _).mp h1
    change e j - 1 + 1 ≤ e (j + 1) at this
    omega
  have hmono' : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ ≤ n → e j₁ ≤ e j₂ := by
    intro j₁ j₂ hle hj₂
    induction j₂, hle using Nat.le_induction with
    | base => exact le_rfl
    | succ j hle ih2 => exact (ih2 (by omega)).trans (hmono j (by omega))

  have hstep : ∀ j, j + 1 < n → p ^ (j + 1) ∣ e (j + 1) - e j := by
    intro j hj
    have h := ih (j + 1) hj (σ := σ) hσ (by omega) (hne (j + 1) (by omega))
    simp only [Nat.add_sub_cancel] at h
    exact (Nat.modEq_iff_dvd' (hmono j (by omega))).mp h

  have hchain : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ + 1 ≤ n → p ^ (j₁ + 1) ∣ e j₂ - e j₁ := by
    intro j₁ j₂ hle hj₂
    induction j₂, hle using Nat.le_induction with
    | base => simp
    | succ j₂ hle ih2 =>
      have h1 := ih2 (by omega)
      have h2 : p ^ (j₁ + 1) ∣ e (j₂ + 1) - e j₂ :=
        (pow_dvd_pow p (by omega)).trans (hstep j₂ (by omega))
      have hm1 := hmono j₂ (by omega)
      have hm2 : e j₁ ≤ e j₂ := hmono' j₁ j₂ hle (by omega)
      have : e (j₂ + 1) - e j₁ = (e (j₂ + 1) - e j₂) + (e j₂ - e j₁) := by omega
      rw [this]
      exact dvd_add h2 h1

  have hmonoN : e (n - 1) ≤ e n := by
    have := hmono (n - 1) (by omega)
    rwa [Nat.sub_add_cancel hn] at this
  have hDprev : p ^ (n - 1) ∣ e n - e (n - 1) := by
    rcases Nat.lt_or_ge 1 n with h1n | hn1
    · have hσp : σ ^ p ∈ lowerRamificationGroup R G 1 := Subgroup.pow_mem _ hσ p
      have hσpn : (σ ^ p) ^ p ^ (n - 1) ≠ 1 := by
        rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hn]; exact hσn
      have h := ih (n - 1) (by omega) (σ := σ ^ p) hσp (by omega) hσpn
      have e1 : (σ ^ p) ^ p ^ (n - 1 - 1) = σ ^ p ^ (n - 1) := by
        rw [← pow_mul, ← pow_succ']; congr 2; omega
      have e2 : (σ ^ p) ^ p ^ (n - 1) = σ ^ p ^ n := by
        rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hn]
      rw [e1, e2] at h
      exact (Nat.modEq_iff_dvd' hmonoN).mp h
    · have : n = 1 := le_antisymm hn1 hn
      subst this
      simp

  rw [Nat.modEq_iff_dvd' hmonoN]
  by_contra hD

  set D : ℕ := e n - e (n - 1) with hDdef
  have hDpos : 0 < D := Nat.pos_of_ne_zero fun h => hD (by rw [h]; exact dvd_zero _)
  have hDndvd : ¬ p ^ n ∣ D := hD

  have hp2 : 2 ≤ p := hp.two_le
  set a : ℕ := (p - 1) * D with hadef
  have hapos : 1 ≤ a := Nat.mul_pos (by omega) hDpos
  have hpa_dvd : p ^ (n - 1) ∣ a := hDprev.mul_left _
  have hpa_ndvd : ¬ p ^ n ∣ a := by
    intro h
    have hcop : (p ^ n).Coprime (p - 1) := by
      refine Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.mpr fun hd => ?_)
      have := Nat.le_of_dvd (by omega) hd
      omega
    rw [hadef] at h
    exact hDndvd (hcop.dvd_of_dvd_mul_left h)
  have hva : padicValNat p a = n - 1 := by
    refine le_antisymm ?_ ((padicValNat_dvd_iff_le (by omega)).mp hpa_dvd)
    by_contra hlt
    push Not at hlt
    exact hpa_ndvd ((padicValNat_dvd_iff_le (by omega)).mpr (by omega))
  have hvpa : padicValNat p (p * a) = n := by
    rw [padicValNat.mul hp.ne_zero (by omega), padicValNat_self, hva]; omega

  obtain ⟨α, hαv, hρα⟩ := IsDiscreteValuationRing.exists_addVal_eq_and_addVal_smul_sub_eq hϖ (σ ^ p) hapos
  have hen : ((e n : ℕ) : ℕ∞) = ramificationDepth R G (σ ^ p ^ n) := coe_toNat_ramificationDepth (hne n le_rfl)
  have hdepth_pa : ramificationDepth R G ((σ ^ p) ^ a) = (e n : ℕ∞) := by
    rw [← pow_mul, depth_pow_eq hp hpR hσ (k := p * a) (by positivity), hvpa, hen]
  set V : ℕ := a - 1 + e n with hVdef
  have hρα' : addVal R (σ ^ p • α - α) = (V : ℕ∞) := by
    have hmemρa : (σ ^ p) ^ a ∈ lowerRamificationGroup R G 0 := by rw [← pow_mul]; exact hmem0 _
    rw [hρα, ← depth_eq_addVal hp hpR hϖ hmemρa, hdepth_pa, hVdef, Nat.cast_add]

  have hαmem : α ∈ (IsLocalRing.maximalIdeal R) ^ a := by
    rw [mem_maximalIdeal_pow_iff_le_addVal, hαv]
  set β : R := ∑ t ∈ Finset.range p, σ ^ t • α with hβdef
  have hβmem : β ∈ (IsLocalRing.maximalIdeal R) ^ (a + 1) := sum_range_smul_mem_pow_succ hpR hσ hαmem
  have hσβ : σ • β - β = σ ^ p • α - α := smul_sum_range_sub σ α p
  have hvσβ : addVal R (σ • β - β) = (V : ℕ∞) := by rw [hσβ, hρα']

  have hγex : ∀ k : ℕ, ∃ γ : R, addVal R γ = k ∧
      (1 ≤ k → addVal R (σ • γ - γ) = ((k - 1 : ℕ) : ℕ∞) + ramificationDepth R G (σ ^ k)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, by simp, fun h => absurd h (by omega)⟩
    · obtain ⟨γ, h1, h2⟩ := IsDiscreteValuationRing.exists_addVal_eq_and_addVal_smul_sub_eq hϖ σ hk
      refine ⟨γ, h1, fun _ => ?_⟩
      rw [h2, ← depth_eq_addVal hp hpR hϖ (hmem0 k)]
  choose γ hγv hγd using hγex

  have haV : a + 1 ≤ V := by have := htwo n le_rfl; omega
  obtain ⟨θ, hθu, hθinv, hrem⟩ :=
    IsDiscreteValuationRing.exists_digits_sub_sum_mem_pow_of_prime_mem hp hpR
      (lowerRamificationGroup_antitone (Nat.zero_le 1) hσ) γ hγv haV (V + 1) hβmem

  set S : Finset ℕ := Finset.Icc (a + 1) V with hSdef
  set r : R := β - ∑ k ∈ S, θ k * γ k with hrdef
  have hr : r ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) := hrem
  have hpt : ∀ k, σ • (θ k * γ k) - θ k * γ k = θ k * (σ • γ k - γ k) + (σ • θ k - θ k) * (σ • γ k) :=
    fun k => by rw [smul_mul']; ring
  have hdec : σ • β - β = (∑ k ∈ S, θ k * (σ • γ k - γ k)) +
      ((∑ k ∈ S, (σ • θ k - θ k) * (σ • γ k)) + (σ • r - r)) := by
    have hβ' : β = ∑ k ∈ S, θ k * γ k + r := by rw [hrdef]; ring
    calc σ • β - β = (σ • (∑ k ∈ S, θ k * γ k) - ∑ k ∈ S, θ k * γ k) + (σ • r - r) := by
            conv_lhs => rw [hβ']
            rw [smul_add]; ring
      _ = (∑ k ∈ S, (σ • (θ k * γ k) - θ k * γ k)) + (σ • r - r) := by
            rw [Finset.smul_sum, Finset.sum_sub_distrib]
      _ = _ := by
            rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib]; ring

  have hE1 : σ • r - r ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) :=
    Submodule.sub_mem _ (IsLocalRing.smul_mem_maximalIdeal_pow_iff.mpr hr) hr
  have hE2 : (∑ k ∈ S, (σ • θ k - θ k) * (σ • γ k)) ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) :=
    Submodule.sum_mem _ fun k _ => Ideal.pow_le_pow_right (by omega) (Ideal.mul_mem_right _ _ (hθinv k))

  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun k => θ k ≠ 0 ∧ ¬ p ^ n ∣ k)
    (fun k => θ k * (σ • γ k - γ k))
  have hE3 : (∑ k ∈ S.filter (fun k => ¬ (θ k ≠ 0 ∧ ¬ p ^ n ∣ k)), θ k * (σ • γ k - γ k)) ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) := by
    refine Submodule.sum_mem _ fun k hk => ?_
    rw [Finset.mem_filter] at hk
    obtain ⟨hkS, hnP⟩ := hk
    have hk1 : a + 1 ≤ k := (Finset.mem_Icc.mp hkS).1
    by_cases hθ0 : θ k = 0
    · simp [hθ0]
    · have hpk : p ^ n ∣ k := by
        by_contra h
        exact hnP ⟨hθ0, h⟩

      have hdk : (e n : ℕ∞) ≤ ramificationDepth R G (σ ^ k) := by
        obtain ⟨q, rfl⟩ := hpk
        rw [pow_mul]
        have h2 := htwo n le_rfl
        have hmem : σ ^ p ^ n ∈ lowerRamificationGroup R G (e n - 1) := by
          rw [mem_iff_succ_le_toNat (hne n le_rfl)]
          change e n - 1 + 1 ≤ e n
          omega
        have := Subgroup.pow_mem _ hmem q
        rw [mem_lowerRamificationGroup_iff_le_ramificationDepth] at this
        calc (e n : ℕ∞) = ((e n - 1 : ℕ) : ℕ∞) + 1 := by norm_cast; omega
          _ ≤ _ := this
      refine Ideal.mul_mem_left _ _ ?_
      rw [mem_maximalIdeal_pow_iff_le_addVal, hγd k (by omega)]
      calc ((V + 1 : ℕ) : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) + ((e n : ℕ) : ℕ∞) := by norm_cast; omega
        _ ≤ ((k - 1 : ℕ) : ℕ∞) + ramificationDepth R G (σ ^ k) := by gcongr

  have hw : ∀ k ∈ S.filter (fun k => θ k ≠ 0 ∧ ¬ p ^ n ∣ k),
      addVal R (θ k * (σ • γ k - γ k)) = ((k - 1 + e (padicValNat p k) : ℕ) : ℕ∞) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hkS, hθ0, hnpk⟩ := hk
    have hk1 : a + 1 ≤ k := (Finset.mem_Icc.mp hkS).1
    have hkne : k ≠ 0 := by omega
    have hj : padicValNat p k ≤ n - 1 := by
      have : ¬ n ≤ padicValNat p k := fun h => hnpk ((padicValNat_dvd_iff_le hkne).mpr h)
      omega
    obtain ⟨u, hu⟩ := (hθu k).resolve_left hθ0
    rw [addVal_mul, ← hu, addVal_eq_zero_of_unit, zero_add, hγd k (by omega),
      depth_pow_eq hp hpR hσ hkne, ← coe_toNat_ramificationDepth (hne _ (by omega))]
    push_cast
    rfl
  have hinj : Set.InjOn (fun k => k - 1 + e (padicValNat p k)) ↑(S.filter (fun k => θ k ≠ 0 ∧ ¬ p ^ n ∣ k)) := by
    intro k₁ hk₁ k₂ hk₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hk₁ hk₂
    have h1 : a + 1 ≤ k₁ := (Finset.mem_Icc.mp hk₁.1).1
    have h2 : a + 1 ≤ k₂ := (Finset.mem_Icc.mp hk₂.1).1
    exact eq_of_w_eq hp e hmono' hchain (by omega) (by omega) hk₁.2.2 hk₂.2.2 h

  have hRest : (∑ k ∈ S.filter (fun k => ¬ (θ k ≠ 0 ∧ ¬ p ^ n ∣ k)), θ k * (σ • γ k - γ k)) +
      ((∑ k ∈ S, (σ • θ k - θ k) * (σ • γ k)) + (σ • r - r)) ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) :=
    Submodule.add_mem _ hE3 (Submodule.add_mem _ hE2 hE1)
  have hEq : σ • β - β = (∑ k ∈ S.filter (fun k => θ k ≠ 0 ∧ ¬ p ^ n ∣ k), θ k * (σ • γ k - γ k)) +
      ((∑ k ∈ S.filter (fun k => ¬ (θ k ≠ 0 ∧ ¬ p ^ n ∣ k)), θ k * (σ • γ k - γ k)) +
        ((∑ k ∈ S, (σ • θ k - θ k) * (σ • γ k)) + (σ • r - r))) := by
    rw [hdec, ← hsplit]; ring
  have hVlt : (V : ℕ∞) < ((V + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self V
  by_cases hemp : S.filter (fun k => θ k ≠ 0 ∧ ¬ p ^ n ∣ k) = ∅
  · have hmem : σ • β - β ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) := by
      rw [hEq, hemp, Finset.sum_empty, zero_add]; exact hRest
    rw [mem_maximalIdeal_pow_iff_le_addVal, hvσβ] at hmem
    exact absurd hmem (not_le.mpr hVlt)
  · obtain ⟨k₀, hk₀, -, hval⟩ := exists_min_addVal_sum_eq _ (Finset.nonempty_of_ne_empty hemp)
      (fun k => θ k * (σ • γ k - γ k)) (fun k => k - 1 + e (padicValNat p k)) hw hinj
    have hk₀' := hk₀
    rw [Finset.mem_filter] at hk₀'
    have hk₀1 : a + 1 ≤ k₀ := (Finset.mem_Icc.mp hk₀'.1).1
    have hneV : k₀ - 1 + e (padicValNat p k₀) ≠ V :=
      w_ne_V hp hn e hmono' hchain hDprev hDndvd hk₀1 hk₀'.2.2
    have hRv : ((V + 1 : ℕ) : ℕ∞) ≤ addVal R ((∑ k ∈ S.filter (fun k => ¬ (θ k ≠ 0 ∧ ¬ p ^ n ∣ k)), θ k * (σ • γ k - γ k)) +
        ((∑ k ∈ S, (σ • θ k - θ k) * (σ • γ k)) + (σ • r - r))) :=
      mem_maximalIdeal_pow_iff_le_addVal.mp hRest
    rcases lt_or_gt_of_ne hneV with hlt | hgt
    ·
      have hlt' : ((k₀ - 1 + e (padicValNat p k₀) : ℕ) : ℕ∞) < ((V + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
      have h1 := addVal_add_eq_of_lt (hval ▸ (hlt'.trans_le hRv))
      rw [← hEq, hvσβ, hval] at h1
      exact absurd h1 (by exact_mod_cast (ne_of_gt hlt))
    ·
      have hbig : (∑ k ∈ S.filter (fun k => θ k ≠ 0 ∧ ¬ p ^ n ∣ k), θ k * (σ • γ k - γ k)) ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) := by
        rw [mem_maximalIdeal_pow_iff_le_addVal, hval]
        exact_mod_cast hgt
      have hmem : σ • β - β ∈ (IsLocalRing.maximalIdeal R) ^ (V + 1) := by rw [hEq]; exact Submodule.add_mem _ hbig hRest
      rw [mem_maximalIdeal_pow_iff_le_addVal, hvσβ] at hmem
      exact absurd hmem (not_le.mpr hVlt)

end S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one
end P2MW
export P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one (solution)
