-- Prove2me | solution 1 for IsDiscreteValuationRing.finsum_lowerRamificationGroup_indicator_comp_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8e659545-a6e3-5e2b-b84c-b8c643d23c29

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
import Theorems.Thm_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

namespace IsLocalRing
p2m_export "IsLocalRing" "maximalIdeal maximalIdeal.isMaximal residue lowerRamificationCard herbrandPhi herbrandPhi_zero herbrandPhi_natCast herbrandPhi_nonneg herbrandPhi_monotone upperRamificationIndex upperRamificationGroup le_herbrandPhi_upperRamificationIndex upperRamificationIndex_le lowerRamificationGroup lowerRamificationGroup_antitone iInf_lowerRamificationGroup_eq_bot"
namespace SwanInfl
p2m_open "IsLocalRing"

p2m_open "IsLocalRing P2MW.S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.IsLocalRing"

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

namespace IsLocalRing
p2m_export "IsLocalRing" "maximalIdeal maximalIdeal.isMaximal residue lowerRamificationCard herbrandPhi herbrandPhi_zero herbrandPhi_natCast herbrandPhi_nonneg herbrandPhi_monotone upperRamificationIndex upperRamificationGroup le_herbrandPhi_upperRamificationIndex upperRamificationIndex_le lowerRamificationGroup lowerRamificationGroup_antitone iInf_lowerRamificationGroup_eq_bot"
namespace SwanInfl
p2m_open "IsLocalRing"

p2m_open "IsLocalRing P2MW.S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.IsLocalRing"

section aux

theorem exists_eq_bot_of_antitone_of_iInf_eq_bot {G : Type*} [Group G] [Finite G] (f : ℕ → Subgroup G) (hf : Antitone f)
    (h : ⨅ i, f i = ⊥) : ∃ N, f N = ⊥ := by
  classical
  haveI : Finite (Subgroup G) := inferInstance
  obtain ⟨s, hs⟩ := (Set.toFinite (Set.range f)).exists_finset_coe

  have hidx : ∀ K ∈ s, ∃ n, f n = K := fun K hK => by
    have : K ∈ Set.range f := by rw [← hs]; exact hK
    exact this
  choose! idx hidx' using hidx
  refine ⟨s.sup idx, le_bot_iff.mp ?_⟩
  rw [← h]
  refine le_iInf fun m => ?_
  have hm : f m ∈ s := by rw [← Finset.mem_coe, hs]; exact ⟨m, rfl⟩
  rw [← hidx' (f m) hm]
  exact hf (Finset.le_sup hm)

theorem eq_of_forall_pos_le_iff {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ v : ℚ, 0 < v → (v ≤ a ↔ v ≤ b)) : a = b := by
  apply le_antisymm
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · exact hb
    · exact (h a ha').mp le_rfl
  · rcases eq_or_lt_of_le hb with rfl | hb'
    · exact ha
    · exact (h b hb').mpr le_rfl

end aux

end IsLocalRing.SwanInfl

open _root_.IsLocalRing _root_.P2MW.S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.IsLocalRing IsLocalRing.SwanInfl in
open scoped Classical in

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] {A : Type*} [CommGroup A] (χ : G ⧸ H →* A) :
    ∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G (i + 1), χ (QuotientGroup.mk σ) = 1 then 0 else 1) =
      ∑ᶠ j : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) 0) : ℚ) *
          (if ∀ τ ∈ IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1), χ τ = 1
            then 0 else 1) := by
  classical

  have hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  obtain ⟨N, hN⟩ := exists_eq_bot_of_antitone_of_iInf_eq_bot (lowerRamificationGroup R G) lowerRamificationGroup_antitone
    (iInf_lowerRamificationGroup_eq_bot hsep)
  have h1 : ∃ N, Triv (R := R) (χ.comp (QuotientGroup.mk' H)) N :=
    ⟨N, fun σ hσ => by rw [hN, Subgroup.mem_bot] at hσ; rw [hσ, map_one]⟩

  have hH := IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField (R := R) (G := G) (H := H) N
  rw [hN, Subgroup.map_bot] at hH
  have h2 : ∃ N', Triv (R := FixedPoints.subring R H) χ N' :=
    ⟨_, fun τ hτ => by rw [← hH, Subgroup.mem_bot] at hτ; rw [hτ, map_one]⟩

  refine (finsum_indicator_eq_herbrandPhi (χ.comp (QuotientGroup.mk' H)) h1).trans
    (Eq.trans ?_ (finsum_indicator_eq_herbrandPhi χ h2).symm)

  have hC := IsDiscreteValuationRing.upperRamificationQuotientCompat_of_isSeparable_residueField (R := R) (G := G) H
  refine eq_of_forall_pos_le_iff (herbrandPhi_nonneg (Nat.cast_nonneg _)) (herbrandPhi_nonneg (Nat.cast_nonneg _)) (fun v hv => ?_)
  rw [← not_triv_upper_iff (χ.comp (QuotientGroup.mk' H)) h1 hv, ← not_triv_upper_iff χ h2 hv, ← hC v hv.le]
  refine not_congr ⟨fun hG τ hτ => ?_, fun hQ σ hσ => hQ _ (Subgroup.mem_map_of_mem _ hσ)⟩
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
  exact hG σ hσ

end S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq
end P2MW
export P2MW.S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq (solution)
