-- Prove2me | solution 1 for IsLocalRing.forall_mem_upperRamificationGroup_iff_finsum_indicator_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5791ddf6-efe6-5465-bcf3-688c0720c3a3

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt

set_option autoImplicit false

namespace IsLocalRing
p2m_export "IsLocalRing" "lowerRamificationCard herbrandPhi herbrandPhi_zero herbrandPhi_natCast herbrandPhi_nonneg herbrandPhi_monotone upperRamificationIndex upperRamificationGroup upperRamificationGroup_of_nonpos le_herbrandPhi_upperRamificationIndex upperRamificationIndex_le lowerRamificationGroup lowerRamificationGroup_antitone"
namespace SwanInfl
p2m_open "IsLocalRing"

p2m_open "IsLocalRing P2MW.S_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt.IsLocalRing"

section generic

variable {R : Type*} [CommRing R] [IsLocalRing R] {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ R]
  {A : Type*} [CommGroup A] (χ : Γ →* A)

def Triv (n : ℕ) : Prop := ∀ σ ∈ lowerRamificationGroup R Γ n, χ σ = 1

omit [Finite Γ] in
theorem Triv.mono {χ : Γ →* A} {m n : ℕ} (hmn : m ≤ n) (hm : Triv (R := R) χ m) : Triv (R := R) χ n :=
  fun σ hσ => hm σ (lowerRamificationGroup_antitone hmn hσ)

variable (R) in

noncomputable def firstTriv (h : ∃ N, Triv (R := R) χ N) : ℕ := by classical exact Nat.find h

omit [Finite Γ] in
theorem triv_iff_firstTriv_le (h : ∃ N, Triv (R := R) χ N) (n : ℕ) : Triv (R := R) χ n ↔ firstTriv R χ h ≤ n := by
  classical
  constructor
  · intro hn; exact Nat.find_min' h hn
  · intro hn; exact (Nat.find_spec h).mono hn

open scoped Classical in

theorem finsum_indicator_eq_herbrandPhi (h : ∃ N, Triv (R := R) χ N) :
    ∑ᶠ i : ℕ, (Nat.card (lowerRamificationGroup R Γ (i + 1)) : ℚ) / (Nat.card (lowerRamificationGroup R Γ 0) : ℚ) *
        (if Triv (R := R) χ (i + 1) then 0 else 1) =
      herbrandPhi R Γ ((firstTriv R χ h - 1 : ℕ) : ℚ) := by
  classical
  set d := firstTriv R χ h with hd
  have hiff : ∀ n, Triv (R := R) χ n ↔ d ≤ n := triv_iff_firstTriv_le χ h

  let t : ℕ → ℚ := fun i => (Nat.card (lowerRamificationGroup R Γ (i + 1)) : ℚ) /
      (Nat.card (lowerRamificationGroup R Γ 0) : ℚ) * (if Triv (R := R) χ (i + 1) then 0 else 1)
  have ht_out : ∀ i, ¬ i + 1 < d → t i = 0 := fun i hi => by
    simp only [t, if_pos ((hiff (i + 1)).mpr (by omega)), mul_zero]
  have ht_in : ∀ i, i + 1 < d → t i = (lowerRamificationCard R Γ (i + 1) : ℚ) / (lowerRamificationCard R Γ 0 : ℚ) := fun i hi => by
    simp only [t, if_neg ((hiff (i + 1)).not.mpr (by omega)), mul_one]
    rfl
  change ∑ᶠ i, t i = _
  rw [finsum_eq_sum_of_support_subset t (s := Finset.range (d - 1)) (by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hni
      exact hi (ht_out i (by omega)))]
  rw [Finset.sum_congr rfl (fun i hi => ht_in i (by rw [Finset.mem_range] at hi; omega)), herbrandPhi_natCast,
    ← Finset.sum_div]
  congr 1
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0]
    simp
  · have hIcc : Finset.Icc 1 (d - 1) = Finset.Ico 1 d := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [add_comm]

theorem upperRamificationIndex_pos {v : ℚ} (hv : 0 < v) : 0 < upperRamificationIndex R Γ v := by
  by_contra h0
  have h0' : upperRamificationIndex R Γ v = 0 := by omega
  have := le_herbrandPhi_upperRamificationIndex (R := R) (G := Γ) v
  rw [h0', Nat.cast_zero, herbrandPhi_zero] at this
  exact absurd this (not_le.mpr hv)

theorem not_triv_upper_iff (h : ∃ N, Triv (R := R) χ N) {v : ℚ} (hv : 0 < v) :
    (¬ ∀ σ ∈ upperRamificationGroup R Γ v, χ σ = 1) ↔ v ≤ herbrandPhi R Γ ((firstTriv R χ h - 1 : ℕ) : ℚ) := by
  set d := firstTriv R χ h with hd
  have hiff : ∀ n, Triv (R := R) χ n ↔ d ≤ n := triv_iff_firstTriv_le χ h
  change ¬ Triv (R := R) χ (upperRamificationIndex R Γ v) ↔ _
  rw [(hiff _).not, not_le]
  have hpos := upperRamificationIndex_pos (R := R) (Γ := Γ) hv
  constructor
  · intro hlt

    refine (le_herbrandPhi_upperRamificationIndex (R := R) (G := Γ) v).trans ?_
    exact (herbrandPhi_monotone (R := R) (G := Γ)) (by exact_mod_cast (show upperRamificationIndex R Γ v ≤ d - 1 by omega))
  · intro hle
    have := upperRamificationIndex_le (R := R) (G := Γ) hle
    omega

end generic

end IsLocalRing.SwanInfl

open _root_.IsLocalRing _root_.P2MW.S_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt.IsLocalRing IsLocalRing.SwanInfl in
open scoped Classical in

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ R]
    {A : Type*} [CommGroup A] (χ : Γ →* A)
    (hfin : ∃ N : ℕ, ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ N, χ σ = 1)
    (hram : ¬ ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ 0, χ σ = 1)
    (u : ℚ) (hu : 0 ≤ u) :
    (∀ σ ∈ IsLocalRing.upperRamificationGroup R Γ u, χ σ = 1) ↔
      ∑ᶠ i : ℕ,
          (Nat.card (IsLocalRing.lowerRamificationGroup R Γ (i + 1)) : ℚ) /
              (Nat.card (IsLocalRing.lowerRamificationGroup R Γ 0) : ℚ) *
            (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ (i + 1), χ σ = 1 then 0 else 1) < u := by
  have h : ∃ N, Triv (R := R) χ N := hfin
  have hd1 : 1 ≤ firstTriv R χ h := by
    by_contra h0
    exact hram ((triv_iff_firstTriv_le χ h 0).mpr (by omega))
  change _ ↔ (∑ᶠ i : ℕ, (Nat.card (lowerRamificationGroup R Γ (i + 1)) : ℚ) / (Nat.card (lowerRamificationGroup R Γ 0) : ℚ) *
      (if Triv (R := R) χ (i + 1) then 0 else 1)) < u
  rw [finsum_indicator_eq_herbrandPhi χ h]
  rcases eq_or_lt_of_le hu with rfl | hu'
  · rw [IsLocalRing.upperRamificationGroup_of_nonpos le_rfl]
    constructor
    · intro h0
      exact absurd h0 hram
    · intro hlt
      exact absurd hlt (not_lt.mpr (herbrandPhi_nonneg (Nat.cast_nonneg _)))
  · rw [← not_iff_not, not_triv_upper_iff χ h hu', not_lt]

end S_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt
end P2MW
export P2MW.S_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt (solution)
