-- Prove2me | solution 1 for IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/17fb7442-15bd-5445-87d4-c3bc09ea88e2

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi
import Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

namespace HerbrandPort

open IsLocalRing

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem lowerRamificationCard_dvd_of_le {i j : ℕ} (h : i ≤ j) :
    lowerRamificationCard R G j ∣ lowerRamificationCard R G i :=
  Subgroup.card_dvd_of_le (lowerRamificationGroup_antitone h)

theorem lowerRamificationCard_dvd_zero (i : ℕ) :
    lowerRamificationCard R G i ∣ lowerRamificationCard R G 0 :=
  lowerRamificationCard_dvd_of_le (Nat.zero_le i)

theorem lowerRamificationCard_dvd_sum_Icc (m : ℕ) :
    lowerRamificationCard R G (m + 1) ∣
      ∑ i ∈ Finset.Icc 1 m, lowerRamificationCard R G i :=
  Finset.dvd_sum fun _i hi =>
    lowerRamificationCard_dvd_of_le ((Finset.mem_Icc.mp hi).2.trans (Nat.le_succ m))

theorem herbrandPhi_natCast_eq_cast_div (m : ℕ) :
    herbrandPhi R G m =
      ((∑ i ∈ Finset.Icc 1 m, lowerRamificationCard R G i : ℕ) : ℚ) /
        (lowerRamificationCard R G 0 : ℚ) := by
  rw [herbrandPhi_natCast, Nat.cast_sum]

theorem sum_Icc_le_mul_of_herbrandPhi_natCast_le [Finite G] {m n : ℕ}
    (h : herbrandPhi R G m ≤ (n : ℚ)) :
    (∑ i ∈ Finset.Icc 1 m, lowerRamificationCard R G i) ≤ n * lowerRamificationCard R G 0 := by
  have hg0 : (0 : ℚ) < (lowerRamificationCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 0)
  rw [herbrandPhi_natCast_eq_cast_div, div_le_iff₀ hg0] at h
  exact_mod_cast h

theorem exists_nat_segment_increment [Finite G] (m n : ℕ)
    (h : herbrandPhi R G m ≤ (n : ℚ)) :
    ∃ j : ℕ, ((n : ℚ) - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ) = (j : ℚ) := by
  have hg0 : (0 : ℚ) < (lowerRamificationCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 0)
  have hgm : (0 : ℚ) < (lowerRamificationCard R G (m + 1) : ℚ) :=
    Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) (m + 1))

  have hle : (∑ i ∈ Finset.Icc 1 m, lowerRamificationCard R G i) ≤
      n * lowerRamificationCard R G 0 :=
    sum_Icc_le_mul_of_herbrandPhi_natCast_le h

  have hdvd : lowerRamificationCard R G (m + 1) ∣
      n * lowerRamificationCard R G 0 - ∑ i ∈ Finset.Icc 1 m, lowerRamificationCard R G i :=
    Nat.dvd_sub ((lowerRamificationCard_dvd_zero (m + 1)).mul_left n)
      (lowerRamificationCard_dvd_sum_Icc m)
  obtain ⟨j, hj⟩ := hdvd
  refine ⟨j, ?_⟩

  have hnum : ((n : ℚ) - herbrandPhi R G m) * (lowerRamificationCard R G 0 : ℚ) =
      ((n * lowerRamificationCard R G 0 -
        ∑ i ∈ Finset.Icc 1 m, lowerRamificationCard R G i : ℕ) : ℚ) := by
    rw [Nat.cast_sub hle, herbrandPhi_natCast_eq_cast_div, sub_mul,
      div_mul_cancel₀ _ hg0.ne', Nat.cast_mul]
  rw [hnum, hj, Nat.cast_mul, mul_div_cancel_left₀ _ hgm.ne']

theorem exists_nat_herbrandPsi_natCast [Finite G] (n : ℕ) :
    ∃ k : ℕ, herbrandPsi R G (n : ℚ) = (k : ℚ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by rw [Nat.cast_zero]; exact herbrandPsi_zero⟩
  ·
    have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    obtain ⟨m, hm⟩ : ∃ m, upperRamificationIndex R G (n : ℚ) = m + 1 := by
      have h0 : upperRamificationIndex R G (n : ℚ) ≠ 0 := by
        rw [Ne, upperRamificationIndex_eq_zero_iff]
        exact not_le.mpr hn'
      exact ⟨upperRamificationIndex R G (n : ℚ) - 1, by omega⟩
    obtain ⟨h1, h2⟩ := (upperRamificationIndex_eq_succ_iff (R := R) (G := G)).mp hm
    obtain ⟨j, hj⟩ := exists_nat_segment_increment m n h1.le
    refine ⟨m + j, ?_⟩
    rw [herbrandPsi_segment m h1.le h2, hj, ← Nat.cast_add]

section Bridge

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

theorem ceil_herbrandPhi_upperRamificationIndex [Finite G]
    (htower : ∀ n : ℕ,
      herbrandPhi R G (n : ℚ) = herbrandPhi S (G ⧸ H) (herbrandPhi R H (n : ℚ)))
    (v : ℚ) :
    ⌈herbrandPhi R H (upperRamificationIndex R G v : ℚ)⌉₊
      = upperRamificationIndex S (G ⧸ H) v := by
  set n := upperRamificationIndex R G v with hn_def
  set k := upperRamificationIndex S (G ⧸ H) v with hk_def
  refine le_antisymm ?le_dir ?ge_dir
  case le_dir =>
    obtain ⟨m, hm⟩ := exists_nat_herbrandPsi_natCast (R := R) (G := H) k
    have hφm : herbrandPhi R H (m : ℚ) = (k : ℚ) := by
      have h := herbrandPhi_herbrandPsi (R := R) (G := H) (k : ℚ)
      rwa [hm] at h
    have hvm : v ≤ herbrandPhi R G (m : ℚ) := by
      rw [htower m, hφm]
      exact le_herbrandPhi_upperRamificationIndex (R := S) (G := G ⧸ H) v
    have hnm : n ≤ m := upperRamificationIndex_le (R := R) (G := G) hvm
    calc ⌈herbrandPhi R H (n : ℚ)⌉₊
        ≤ ⌈herbrandPhi R H (m : ℚ)⌉₊ :=
          Nat.ceil_le_ceil
            (herbrandPhi_monotone (R := R) (G := H) (Nat.cast_le.mpr hnm))
      _ = k := by rw [hφm, Nat.ceil_natCast]
  case ge_dir =>
    refine upperRamificationIndex_le (R := S) (G := G ⧸ H) ?_
    calc v ≤ herbrandPhi R G (n : ℚ) :=
            le_herbrandPhi_upperRamificationIndex (R := R) (G := G) v
      _ = herbrandPhi S (G ⧸ H) (herbrandPhi R H (n : ℚ)) := htower n
      _ ≤ herbrandPhi S (G ⧸ H) ((⌈herbrandPhi R H (n : ℚ)⌉₊ : ℕ) : ℚ) :=
            herbrandPhi_monotone (R := S) (G := G ⧸ H) (Nat.le_ceil _)

end Bridge

end IsLocalRing

end HerbrandPort

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup S (G ⧸ H) ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊) :
    IsLocalRing.UpperRamificationQuotientCompat R G S H := by

  have htower : ∀ n : ℕ, IsLocalRing.herbrandPhi R G (n : ℚ) =
      IsLocalRing.herbrandPhi S (G ⧸ H) (IsLocalRing.herbrandPhi R H (n : ℚ)) := fun n =>
    IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
      hH (Nat.cast_nonneg n)
  intro v _hv
  show (IsLocalRing.lowerRamificationGroup R G (IsLocalRing.upperRamificationIndex R G v)).map
        (QuotientGroup.mk' H)
      = IsLocalRing.lowerRamificationGroup S (G ⧸ H)
          (IsLocalRing.upperRamificationIndex S (G ⧸ H) v)
  rw [← HerbrandPort.IsLocalRing.ceil_herbrandPhi_upperRamificationIndex htower v]
  exact hH (IsLocalRing.upperRamificationIndex R G v)

end S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
end P2MW
export P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq (solution)
