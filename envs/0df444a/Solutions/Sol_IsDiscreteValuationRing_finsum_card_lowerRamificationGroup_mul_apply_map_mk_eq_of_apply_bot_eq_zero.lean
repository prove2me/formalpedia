-- Prove2me | solution 1 for IsDiscreteValuationRing.finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a78e1b3c-452d-5eec-94c3-4e22885f52d9

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
import Theorems.Thm_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

namespace L1Body

open IsLocalRing

section generic
variable {R : Type*} [CommRing R] [IsLocalRing R] {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ R]

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
  · rcases eq_or_lt_of_le ha with h0 | hpos
    · rw [← h0]; exact hb
    · exact (h a hpos).1 le_rfl
  · rcases eq_or_lt_of_le hb with h0 | hpos
    · rw [← h0]; exact ha
    · exact (h b hpos).2 le_rfl

theorem upperRamificationIndex_pos {v : ℚ} (hv : 0 < v) : 0 < upperRamificationIndex R Γ v := by
  by_contra h0
  have h0' : upperRamificationIndex R Γ v = 0 := by omega
  have := le_herbrandPhi_upperRamificationIndex (R := R) (G := Γ) v
  rw [h0', Nat.cast_zero, herbrandPhi_zero] at this
  exact absurd this (not_le.mpr hv)

theorem upperRamificationIndex_le_iff {v : ℚ} {n : ℕ} :
    upperRamificationIndex R Γ v ≤ n ↔ v ≤ herbrandPhi R Γ n := by
  constructor
  · intro h
    exact (le_herbrandPhi_upperRamificationIndex (R := R) (G := Γ) v).trans
      ((herbrandPhi_monotone (R := R) (G := Γ)) (by exact_mod_cast h))
  · exact fun h => upperRamificationIndex_le h

theorem sum_range_card_div_eq_herbrandPhi (n : ℕ) :
    ∑ i ∈ Finset.range n, (Nat.card (lowerRamificationGroup R Γ (i + 1)) : ℚ) /
        (Nat.card (lowerRamificationGroup R Γ 0) : ℚ) = herbrandPhi R Γ n := by
  rw [herbrandPhi_natCast, ← Finset.sum_div]
  congr 1
  have : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [add_comm]
  rfl

end generic

end L1Body

open L1Body IsLocalRing in
set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] (f : Subgroup (G ⧸ H) → ℚ) (hf : f ⊥ = 0) :
    (IsLocalRing.lowerRamificationGroup R G 0).map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) 0 ∧
    ∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          f ((IsLocalRing.lowerRamificationGroup R G (i + 1)).map (QuotientGroup.mk' H)) =
      ∑ᶠ j : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) 0) : ℚ) *
          f (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) := by
  classical

  set P : ℕ → Subgroup G := fun i => lowerRamificationGroup R G i with hP
  set Q : ℕ → Subgroup (G ⧸ H) := fun j => lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) j with hQ
  set c : ℕ → ℕ := fun n => ⌈herbrandPhi R H (n : ℚ)⌉₊ with hc

  have hmap : ∀ n : ℕ, (P n).map (QuotientGroup.mk' H) = Q (c n) := fun n =>
    IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField (R := R) (G := G) (H := H) n
  have hC := IsDiscreteValuationRing.upperRamificationQuotientCompat_of_isSeparable_residueField (R := R) (G := G) H
  have hc0 : c 0 = 0 := by simp only [hc, Nat.cast_zero, herbrandPhi_zero, Nat.ceil_zero]
  have hcmono : Monotone c := fun a b hab => Nat.ceil_mono ((herbrandPhi_monotone (R := R) (G := H)) (by exact_mod_cast hab))
  have hc1 : ∀ n : ℕ, 1 ≤ c (n + 1) := fun n => by
    have : (0 : ℚ) < herbrandPhi R H ((n + 1 : ℕ) : ℚ) := herbrandPhi_pos (by exact_mod_cast Nat.succ_pos n)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr this))
  refine ⟨by have h := hmap 0; rwa [hc0] at h, ?_⟩

  have hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  obtain ⟨N, hN⟩ := exists_eq_bot_of_antitone_of_iInf_eq_bot (lowerRamificationGroup R G) lowerRamificationGroup_antitone
    (iInf_lowerRamificationGroup_eq_bot hsep)
  have hPanti : Antitone P := lowerRamificationGroup_antitone
  have hQanti : Antitone Q := lowerRamificationGroup_antitone
  have hPN : ∀ i, N ≤ i → P i = ⊥ := fun i hi => le_bot_iff.mp (hN ▸ hPanti hi)
  set M := c N with hM
  have hQM : ∀ j, M ≤ j → Q j = ⊥ := fun j hj => by
    apply le_bot_iff.mp
    have h1 : Q M = ⊥ := by rw [hM, ← hmap N, hPN N le_rfl, Subgroup.map_bot]
    rw [← h1]; exact hQanti hj

  set w : ℕ → ℚ := fun i => (Nat.card (P (i + 1)) : ℚ) / (Nat.card (P 0) : ℚ) with hw
  set wq : ℕ → ℚ := fun j => (Nat.card (Q (j + 1)) : ℚ) / (Nat.card (Q 0) : ℚ) with hwq
  have hwsum : ∀ n, ∑ i ∈ Finset.range n, w i = herbrandPhi R G n := fun n => sum_range_card_div_eq_herbrandPhi n
  have hwqsum : ∀ n, ∑ j ∈ Finset.range n, wq j = herbrandPhi (FixedPoints.subring R H) (G ⧸ H) n := fun n =>
    sum_range_card_div_eq_herbrandPhi n

  set Δ : ℕ → ℚ := fun k => f (Q k) - f (Q (k + 1)) with hΔ
  have htel : ∀ m : ℕ, m ≤ M → f (Q m) = ∑ k ∈ Finset.Ico m M, Δ k := by
    intro m hm
    rw [Finset.sum_Ico_eq_sum_range]
    have h1 : ∑ k ∈ Finset.range (M - m), Δ (m + k) =
        ∑ i ∈ Finset.range (M - m), (f (Q (m + i)) - f (Q (m + (i + 1)))) :=
      Finset.sum_congr rfl (fun i _ => by simp only [hΔ, Nat.add_assoc])
    rw [h1, Finset.sum_range_sub', add_zero, Nat.add_sub_cancel' hm, hQM M le_rfl, hf, sub_zero]

  have hL : ∑ᶠ i : ℕ, w i * f ((P (i + 1)).map (QuotientGroup.mk' H)) =
      ∑ i ∈ Finset.range N, w i * f ((P (i + 1)).map (QuotientGroup.mk' H)) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hi
    rw [hPN (i + 1) (by omega), Subgroup.map_bot, hf, mul_zero]
  have hR : ∑ᶠ j : ℕ, wq j * f (Q (j + 1)) = ∑ j ∈ Finset.range M, wq j * f (Q (j + 1)) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hj
    rw [hQM (j + 1) (by omega), hf, mul_zero]
  change ∑ᶠ i : ℕ, w i * f ((P (i + 1)).map (QuotientGroup.mk' H)) = ∑ᶠ j : ℕ, wq j * f (Q (j + 1))
  rw [hL, hR]

  have hci : ∀ i, i < N → c (i + 1) ≤ M := fun i hi => hcmono (by omega)
  have hL2 : ∑ i ∈ Finset.range N, w i * f ((P (i + 1)).map (QuotientGroup.mk' H)) =
      ∑ k ∈ Finset.Ico 1 M, Δ k * ∑ i ∈ (Finset.range N).filter (fun i => c (i + 1) ≤ k), w i := by
    calc ∑ i ∈ Finset.range N, w i * f ((P (i + 1)).map (QuotientGroup.mk' H))
        = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.Ico (c (i + 1)) M, w i * Δ k := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          rw [hmap, htel _ (hci i hi), Finset.mul_sum]
      _ = ∑ k ∈ Finset.Ico 1 M, ∑ i ∈ (Finset.range N).filter (fun i => c (i + 1) ≤ k), w i * Δ k := by
          apply Finset.sum_comm'
          intro i k
          simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]
          constructor
          · rintro ⟨hi, hk1, hk2⟩; exact ⟨⟨hi, hk1⟩, (hc1 i).trans hk1, hk2⟩
          · rintro ⟨⟨hi, hk1⟩, -, hk2⟩; exact ⟨hi, hk1, hk2⟩
      _ = ∑ k ∈ Finset.Ico 1 M, Δ k * ∑ i ∈ (Finset.range N).filter (fun i => c (i + 1) ≤ k), w i := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
  have hR2 : ∑ j ∈ Finset.range M, wq j * f (Q (j + 1)) = ∑ k ∈ Finset.Ico 1 M, Δ k * ∑ j ∈ Finset.range k, wq j := by
    calc ∑ j ∈ Finset.range M, wq j * f (Q (j + 1))
        = ∑ j ∈ Finset.range M, ∑ k ∈ Finset.Ico (j + 1) M, wq j * Δ k := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [Finset.mem_range] at hj
          rw [htel _ (by omega), Finset.mul_sum]
      _ = ∑ k ∈ Finset.Ico 1 M, ∑ j ∈ Finset.range k, wq j * Δ k := by
          apply Finset.sum_comm'
          intro j k
          simp only [Finset.mem_range, Finset.mem_Ico]
          constructor
          · rintro ⟨hj, hk1, hk2⟩; exact ⟨hk1, by omega, hk2⟩
          · rintro ⟨hjk, hk1, hk2⟩; exact ⟨by omega, hjk, hk2⟩
      _ = ∑ k ∈ Finset.Ico 1 M, Δ k * ∑ j ∈ Finset.range k, wq j := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
  rw [hL2, hR2]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk

  by_cases hjump : Q (k + 1) = Q k
  · have : Δ k = 0 := by simp only [hΔ, hjump, sub_self]
    rw [this, zero_mul, zero_mul]
  congr 1

  have hex : ∃ i, ¬ c (i + 1) ≤ k := ⟨N - 1, by
    have hN1 : 1 ≤ N := by
      by_contra h0
      have : N = 0 := by omega
      rw [hM, this, hc0] at hk
      omega
    rw [Nat.sub_add_cancel hN1]; omega⟩
  set nk := Nat.find hex with hnk
  have hnk_spec : ¬ c (nk + 1) ≤ k := Nat.find_spec hex
  have hnk_min : ∀ i, i < nk → c (i + 1) ≤ k := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this
  have hnkN : nk ≤ N - 1 := Nat.find_le (by
    have hN1 : 1 ≤ N := by
      by_contra h0
      have : N = 0 := by omega
      rw [hM, this, hc0] at hk
      omega
    rw [Nat.sub_add_cancel hN1]; omega)
  have hfilter : (Finset.range N).filter (fun i => c (i + 1) ≤ k) = Finset.range nk := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hi⟩
      by_contra hin
      exact hnk_spec ((hcmono (by omega)).trans hi)
    · intro hi
      exact ⟨by omega, hnk_min i hi⟩
  rw [hfilter, hwsum, hwqsum]

  have hcle : ∀ m, m ≤ nk → c m ≤ k := by
    intro m hm
    rcases m with _ | m
    · rw [hc0]; exact Nat.zero_le _
    · exact hnk_min m (by omega)
  have hcgt : ∀ m, nk < m → k + 1 ≤ c m := by
    intro m hm
    have h1 : c (nk + 1) ≤ c m := hcmono (by omega)
    omega
  have hstrict : Q (k + 1) < Q k := lt_of_le_of_ne (hQanti (Nat.le_succ k)) hjump
  refine eq_of_forall_pos_le_iff (herbrandPhi_nonneg (Nat.cast_nonneg _)) (herbrandPhi_nonneg (Nat.cast_nonneg _)) (fun v hv => ?_)
  rw [← upperRamificationIndex_le_iff, ← upperRamificationIndex_le_iff]

  have hstar : Q (c (upperRamificationIndex R G v)) = Q (upperRamificationIndex (FixedPoints.subring R H) (G ⧸ H) v) := by
    rw [← hmap]
    exact hC v hv.le
  constructor
  · intro hle
    by_contra hgt
    push Not at hgt
    have h1 : Q (upperRamificationIndex (FixedPoints.subring R H) (G ⧸ H) v) ≤ Q (k + 1) := hQanti (by omega)
    have h2 : Q k ≤ Q (c (upperRamificationIndex R G v)) := hQanti (hcle _ hle)
    rw [hstar] at h2
    exact absurd (lt_of_lt_of_le (lt_of_le_of_lt h2 (lt_of_le_of_lt h1 hstrict)) le_rfl) (lt_irrefl _)
  · intro hle
    by_contra hgt
    push Not at hgt
    have h1 : Q (c (upperRamificationIndex R G v)) ≤ Q (k + 1) := hQanti (hcgt _ hgt)
    have h2 : Q k ≤ Q (upperRamificationIndex (FixedPoints.subring R H) (G ⧸ H) v) := hQanti hle
    rw [← hstar] at h2
    exact absurd (lt_of_lt_of_le (lt_of_le_of_lt h2 (lt_of_le_of_lt h1 hstrict)) le_rfl) (lt_irrefl _)

end S_IsDiscreteValuationRing_finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero
end P2MW
export P2MW.S_IsDiscreteValuationRing_finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero (solution)
