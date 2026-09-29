-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_finsum_lowerRamificationGroup_indicator_eq_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/82c97929-cded-5e7c-8614-8f6427ba2c98

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild
import Theorems.Thm_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq
import Theorems.Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
import Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

namespace IsLocalRing
p2m_export "IsLocalRing" "ResidueField maximalIdeal maximalIdeal.isMaximal residue lowerRamificationCard lowerRamificationCard_pos herbrandPhi herbrandPhi_zero herbrandPhi_natCast herbrandPhi_monotone upperRamificationIndex upperRamificationGroup le_herbrandPhi_upperRamificationIndex upperRamificationIndex_le lowerRamificationGroup lowerRamificationGroup_antitone iInf_lowerRamificationGroup_eq_bot"
namespace SwanInfl
p2m_open "IsLocalRing~exists_lowerRamificationGroup_eq_bot"

p2m_open "IsLocalRing~exists_lowerRamificationGroup_eq_bot P2MW.S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.IsLocalRing"

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
p2m_export "IsLocalRing" "ResidueField maximalIdeal maximalIdeal.isMaximal residue lowerRamificationCard lowerRamificationCard_pos herbrandPhi herbrandPhi_zero herbrandPhi_natCast herbrandPhi_monotone upperRamificationIndex upperRamificationGroup le_herbrandPhi_upperRamificationIndex upperRamificationIndex_le lowerRamificationGroup lowerRamificationGroup_antitone iInf_lowerRamificationGroup_eq_bot"
namespace SwanInfl
p2m_open "IsLocalRing~exists_lowerRamificationGroup_eq_bot"

p2m_open "IsLocalRing~exists_lowerRamificationGroup_eq_bot P2MW.S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.IsLocalRing"

theorem exists_eq_bot_of_antitone_of_iInf_eq_bot {G : Type*} [Group G] [Finite G] (f : ℕ → Subgroup G) (hf : Antitone f)
    (h : ⨅ i, f i = ⊥) : ∃ N, f N = ⊥ := by
  classical
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

theorem exists_lowerRamificationGroup_eq_bot {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ S] [FaithfulSMul Γ S] :
    ∃ N, lowerRamificationGroup S Γ N = ⊥ := by
  have hsep : ⨅ n, (IsLocalRing.maximalIdeal S) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  exact exists_eq_bot_of_antitone_of_iInf_eq_bot (lowerRamificationGroup S Γ) lowerRamificationGroup_antitone
    (iInf_lowerRamificationGroup_eq_bot hsep)

end IsLocalRing.SwanInfl

p2m_open "IsLocalRing~exists_lowerRamificationGroup_eq_bot" in open _root_.P2MW.S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.IsLocalRing IsLocalRing.SwanInfl in
open scoped Classical in

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (ψ : G →* ℂˣ) :
    ∃ m : ℕ,
      ∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G (i + 1), ψ σ = 1 then 0 else 1) = m := by

  have hA := IsDiscreteValuationRing.finsum_lowerRamificationGroup_indicator_comp_mk_eq (R := R) (G := G) ψ.ker (QuotientGroup.kerLift ψ)
  have e1 : (∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G (i + 1), ψ σ = 1 then 0 else 1)) =
      ∑ᶠ j : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (j + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) 0) : ℚ) *
          (if ∀ τ ∈ IsLocalRing.lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (j + 1), QuotientGroup.kerLift ψ τ = 1
            then 0 else 1) := by
    refine Eq.trans (finsum_congr fun i => congrArg₂ (· * ·) rfl (@if_congr ℚ _ _ (_) (_) _ _ _ _ ?_ rfl rfl)) hA
    exact forall₂_congr fun σ _ => by rw [QuotientGroup.kerLift_mk]
  rw [e1]

  haveI : IsDiscreteValuationRing (FixedPoints.subring R ψ.ker) := FixedPoints.isDiscreteValuationRing_subring
  obtain ⟨hfaith, hperf, hlies, hsep⟩ :=
    FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring (R := R) (G := G) ψ.ker
  haveI := hfaith
  haveI := hperf
  haveI := hlies
  haveI := hsep
  haveI : IsCyclic (G ⧸ ψ.ker) :=
    isCyclic_of_subgroup_isDomain ((Units.coeHom ℂ).comp (QuotientGroup.kerLift ψ))
      (fun a b h => QuotientGroup.kerLift_injective ψ (Units.ext h))
  have hHA := IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic (R := FixedPoints.subring R ψ.ker) (G := G ⧸ ψ.ker)

  have hinj := QuotientGroup.kerLift_injective ψ
  have htriv : ∀ n, Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) n ↔
      lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) n = ⊥ := fun n => by
    rw [Subgroup.eq_bot_iff_forall]
    refine forall₂_congr fun τ _ => ⟨fun h => hinj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot (S := FixedPoints.subring R ψ.ker) (Γ := G ⧸ ψ.ker)
  have hfin : ∃ N, Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) N := ⟨N, (htriv N).2 hN⟩
  have e2 := finsum_indicator_eq_herbrandPhi (QuotientGroup.kerLift ψ) hfin
  unfold Triv at e2
  rw [e2]
  set d := firstTriv (FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) hfin with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · refine ⟨0, ?_⟩
    rw [hd0]
    simp
  ·
    have hjump : lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (d - 1) ≠
        lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (d - 1 + 1) := by
      rw [Nat.sub_add_cancel hdpos]
      intro h
      have h1 : ¬ Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) (d - 1) :=
        fun ht => by have := (triv_iff_firstTriv_le _ hfin (d - 1)).1 ht; omega
      have h2 : Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) d := (triv_iff_firstTriv_le _ hfin d).2 le_rfl
      exact h1 ((htriv _).2 (h.trans ((htriv _).1 h2)))
    obtain ⟨m, hm⟩ := hHA (d - 1) hjump
    refine ⟨m, ?_⟩
    rw [herbrandPhi_natCast]
    unfold lowerRamificationCard
    have h0 : (Nat.card (lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) 0) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (lowerRamificationCard_pos (R := FixedPoints.subring R ψ.ker) (G := G ⧸ ψ.ker) 0).ne'
    rw [div_eq_iff h0]
    exact_mod_cast (by rw [hm, mul_comm] : (∑ j ∈ Finset.Icc 1 (d - 1), Nat.card (lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) j)) = m * Nat.card (lowerRamificationGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) 0))

end S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast (solution)
