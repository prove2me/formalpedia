-- Prove2me | solution 1 for IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/50ac0ff9-2ff8-5774-a440-2a9b4a95c370

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq

set_option autoImplicit false

namespace HerbrandPort

open IsLocalRing

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

variable (R) in

noncomputable def herbrandPhiCeil (H : Type*) [Group H] [MulSemiringAction H R] (n : ℕ) : ℕ :=
  sInf {k : ℕ | herbrandPhi R H (n : ℚ) ≤ (k : ℚ)}

section HerbrandPhiCeil

variable {H : Type*} [Group H] [MulSemiringAction H R]

theorem herbrandPhiCeil_eq_ceil (n : ℕ) :
    herbrandPhiCeil R H n = ⌈herbrandPhi R H (n : ℚ)⌉₊ := by
  have hset : {k : ℕ | herbrandPhi R H (n : ℚ) ≤ (k : ℚ)} =
      Set.Ici ⌈herbrandPhi R H (n : ℚ)⌉₊ :=
    Set.ext fun k => by rw [Set.mem_setOf_eq, Set.mem_Ici, Nat.ceil_le]
  show sInf {k : ℕ | herbrandPhi R H (n : ℚ) ≤ (k : ℚ)} = ⌈herbrandPhi R H (n : ℚ)⌉₊
  rw [hset, csInf_Ici]

@[scoped simp] theorem herbrandPhiCeil_zero : herbrandPhiCeil R H 0 = 0 := by
  rw [herbrandPhiCeil_eq_ceil, Nat.cast_zero, herbrandPhi_zero, Nat.ceil_zero]

end HerbrandPhiCeil

variable (R G) in

def LowerHerbrandQuotientCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ n : ℕ,
    (lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      lowerRamificationGroup S (G ⧸ H) (herbrandPhiCeil R H n)

variable (R G) in

def HerbrandPhiTowerCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ u : ℚ, 0 ≤ u →
    herbrandPhi R G u = herbrandPhi S (G ⧸ H) (herbrandPhi R H u)

section TowerCompat

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

theorem herbrandPhi_tower_zero :
    herbrandPhi R G (0 : ℚ) = herbrandPhi S (G ⧸ H) (herbrandPhi R H (0 : ℚ)) := by
  simp

namespace HerbrandPhiTowerCompat

theorem natCast (h : HerbrandPhiTowerCompat R G S H) (n : ℕ) :
    herbrandPhi R G (n : ℚ) = herbrandPhi S (G ⧸ H) (herbrandPhi R H (n : ℚ)) :=
  h n (Nat.cast_nonneg n)

end HerbrandPhiTowerCompat

end TowerCompat

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

theorem one_le_herbrandPhiCeil_succ [Finite G] (m : ℕ) :
    1 ≤ herbrandPhiCeil R G (m + 1) := by
  rw [herbrandPhiCeil_eq_ceil, Nat.one_le_ceil_iff]
  exact_mod_cast herbrandPhi_pos (R := R) (G := G)
    (Nat.cast_pos.mpr (Nat.succ_pos m))

theorem herbrandPhiCeil_succ_cast_sub_one_le [Finite G] (m : ℕ) :
    (herbrandPhiCeil R G (m + 1) : ℚ) - 1 ≤ herbrandPhi R G (m : ℚ) := by
  have hg0 : 0 < lowerRamificationCard R G 0 := lowerRamificationCard_pos 0
  have hg0' : (0 : ℚ) < (lowerRamificationCard R G 0 : ℚ) := Nat.cast_pos.mpr hg0

  set h0 := lowerRamificationCard R G 0 with hh0
  set hm1 := lowerRamificationCard R G (m + 1) with hhm1
  set Sm := ∑ i ∈ Finset.Icc 1 m, lowerRamificationCard R G i with hSm
  have hSm1 : ∑ i ∈ Finset.Icc 1 (m + 1), lowerRamificationCard R G i = Sm + hm1 :=
    Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)) _

  have hdvd0 : hm1 ∣ h0 := lowerRamificationCard_dvd_zero (m + 1)
  have hdvdS : hm1 ∣ Sm := lowerRamificationCard_dvd_sum_Icc m

  have hCeq : herbrandPhiCeil R G (m + 1) = ⌈((Sm + hm1 : ℕ) : ℚ) / (h0 : ℚ)⌉₊ := by
    rw [herbrandPhiCeil_eq_ceil, herbrandPhi_natCast_eq_cast_div, hSm1]
  set C := ⌈((Sm + hm1 : ℕ) : ℚ) / (h0 : ℚ)⌉₊ with hC

  have hNatIneq : C * h0 ≤ Sm + h0 := by

    have hCge : Sm + hm1 ≤ C * h0 := by
      have h1 : ((Sm + hm1 : ℕ) : ℚ) ≤ (C : ℚ) * h0 :=
        (div_le_iff₀ hg0').mp (Nat.le_ceil _)
      have h2 : ((Sm + hm1 : ℕ) : ℚ) ≤ ((C * h0 : ℕ) : ℚ) := by
        push_cast at h1 ⊢; linarith
      exact_mod_cast h2

    have hClt : C * h0 < Sm + hm1 + h0 := by
      have h1 : (C : ℚ) < ((Sm + hm1 : ℕ) : ℚ) / h0 + 1 :=
        Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) hg0'.le)
      have h2 : (C : ℚ) * h0 < ((Sm + hm1 : ℕ) : ℚ) + h0 := by
        have h3 := mul_lt_mul_of_pos_right h1 hg0'
        rw [add_one_mul, div_mul_cancel₀ _ hg0'.ne'] at h3; exact h3
      have h4 : ((C * h0 : ℕ) : ℚ) < ((Sm + hm1 + h0 : ℕ) : ℚ) := by
        push_cast at h2 ⊢; linarith
      exact_mod_cast h4

    have hdvd_diff : hm1 ∣ C * h0 - (Sm + hm1) :=
      Nat.dvd_sub (Dvd.dvd.mul_left hdvd0 C) (hdvdS.add (dvd_refl hm1))
    have hpos : 0 < h0 - (C * h0 - (Sm + hm1)) := by omega
    have hmle : hm1 ≤ h0 - (C * h0 - (Sm + hm1)) :=
      Nat.le_of_dvd hpos (Nat.dvd_sub hdvd0 hdvd_diff)
    omega

  rw [hCeq, herbrandPhi_natCast_eq_cast_div, ← hh0, ← hSm, le_div_iff₀ hg0']
  have hCast : (C : ℚ) * (h0 : ℚ) ≤ (Sm : ℚ) + (h0 : ℚ) := by
    have h := Nat.cast_le (α := ℚ).mpr hNatIneq; push_cast at h; linarith
  linarith

section Card

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

theorem card_lowerRamificationGroup_map_mul_card_subgroup (n : ℕ) :
    Nat.card ((lowerRamificationGroup R G n).map (QuotientGroup.mk' H)) *
        lowerRamificationCard R H n =
      lowerRamificationCard R G n := by

  set Gn := lowerRamificationGroup R G n with hGn
  let f : Gn →* G ⧸ H := (QuotientGroup.mk' H).comp Gn.subtype

  have hrange : f.range = Gn.map (QuotientGroup.mk' H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = H.subgroupOf Gn := by
    rw [show f.ker = ((QuotientGroup.mk' H).ker).subgroupOf Gn from rfl,
      QuotientGroup.ker_mk']

  have hLagrange : Nat.card Gn = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker

  have hker_card : Nat.card f.ker = lowerRamificationCard R H n := by
    have h1 : (f.ker).map Gn.subtype = H ⊓ Gn := by
      rw [hker, Subgroup.subgroupOf_map_subtype, inf_comm]
    have h2 := lowerRamificationGroup_map_subtype' (R := R) H n
    rw [← hGn] at h2
    calc Nat.card f.ker
        = Nat.card ((f.ker).map Gn.subtype) :=
          Nat.card_congr (Subgroup.equivMapOfInjective _ _ Gn.subtype_injective).toEquiv
      _ = Nat.card ((lowerRamificationGroup R H n).map H.subtype) := by rw [h1, h2]
      _ = lowerRamificationCard R H n :=
          (Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ H.subtype_injective).toEquiv).symm
  rw [show lowerRamificationCard R G n = Nat.card Gn from rfl, hLagrange, hrange, hker_card]

theorem LowerHerbrandQuotientCompat.lowerRamificationCard_quotient_mul
    (hc : LowerHerbrandQuotientCompat R G S H) (n : ℕ) :
    (lowerRamificationCard S (G ⧸ H) (herbrandPhiCeil R H n) : ℚ) *
        (lowerRamificationCard R H n : ℚ) =
      (lowerRamificationCard R G n : ℚ) := by
  have h := card_lowerRamificationGroup_map_mul_card_subgroup (R := R) (G := G) (H := H) n
  have hcard :
      lowerRamificationCard S (G ⧸ H) (herbrandPhiCeil R H n) =
        Nat.card ((lowerRamificationGroup R G n).map (QuotientGroup.mk' H)) := by
    unfold lowerRamificationCard; rw [← hc n]
  rw [hcard]; exact_mod_cast h

end Card

section Tower

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

variable [Finite G]

theorem herbrandPhi_mem_segment_phiCeil_succ (m : ℕ) :
    let j := herbrandPhiCeil R H (m + 1) - 1
    ((j : ℚ) ≤ herbrandPhi R H (m : ℚ) ∧ herbrandPhi R H (m : ℚ) ≤ (j : ℚ) + 1) ∧
      ((j : ℚ) ≤ herbrandPhi R H ((m : ℚ) + 1) ∧
        herbrandPhi R H ((m : ℚ) + 1) ≤ (j : ℚ) + 1) := by
  have h1 := one_le_herbrandPhiCeil_succ (R := R) (G := H) m
  have hcast : ((herbrandPhiCeil R H (m + 1) - 1 : ℕ) : ℚ) =
      (herbrandPhiCeil R H (m + 1) : ℚ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hkey := herbrandPhiCeil_succ_cast_sub_one_le (R := R) (G := H) m
  have hceil : herbrandPhi R H ((m : ℚ) + 1) ≤ (herbrandPhiCeil R H (m + 1) : ℚ) := by
    rw [herbrandPhiCeil_eq_ceil, show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by push_cast; ring]
    exact Nat.le_ceil _
  have hmono : herbrandPhi R H (m : ℚ) ≤ herbrandPhi R H ((m : ℚ) + 1) :=
    herbrandPhi_monotone (by linarith)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hcast]; exact hkey
  · rw [hcast]; linarith
  · rw [hcast]; linarith
  · rw [hcast]; linarith

theorem LowerHerbrandQuotientCompat.herbrandPhi_comp_segment
    (hc : LowerHerbrandQuotientCompat R G S H) (m : ℕ) {u : ℚ}
    (hum : (m : ℚ) ≤ u) (hum1 : u ≤ (m : ℚ) + 1) :
    herbrandPhi S (G ⧸ H) (herbrandPhi R H u) -
        herbrandPhi S (G ⧸ H) (herbrandPhi R H (m : ℚ)) =
      (u - m) * (lowerRamificationCard R G (m + 1) : ℚ) /
        (lowerRamificationCard R G 0 : ℚ) := by
  obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ :=
    herbrandPhi_mem_segment_phiCeil_succ (R := R) (G := G) (H := H) m
  set j := herbrandPhiCeil R H (m + 1) - 1 with hj
  have hj1 : j + 1 = herbrandPhiCeil R H (m + 1) :=
    Nat.sub_add_cancel (one_le_herbrandPhiCeil_succ (R := R) (G := H) m)

  have hHu_lo : (j : ℚ) ≤ herbrandPhi R H u := ha1.trans (herbrandPhi_monotone hum)
  have hHu_hi : herbrandPhi R H u ≤ (j : ℚ) + 1 := (herbrandPhi_monotone hum1).trans hb2

  have hchord :
      herbrandPhi S (G ⧸ H) (herbrandPhi R H u) -
          herbrandPhi S (G ⧸ H) (herbrandPhi R H (m : ℚ)) =
        (herbrandPhi R H u - herbrandPhi R H (m : ℚ)) *
          ((lowerRamificationCard S (G ⧸ H) (herbrandPhiCeil R H (m + 1)) : ℚ) /
            (lowerRamificationCard S (G ⧸ H) 0 : ℚ)) := by
    rw [herbrandPhi_segment j hHu_lo hHu_hi, herbrandPhi_segment j ha1 ha2, hj1]; ring

  have hHinc : herbrandPhi R H u - herbrandPhi R H (m : ℚ) =
      (u - m) *
        ((lowerRamificationCard R H (m + 1) : ℚ) / (lowerRamificationCard R H 0 : ℚ)) := by
    rw [herbrandPhi_segment m hum hum1]; ring
  rw [hchord, hHinc]

  have hcard0 := hc.lowerRamificationCard_quotient_mul 0
  rw [herbrandPhiCeil_zero] at hcard0
  have hcardm1 := hc.lowerRamificationCard_quotient_mul (m + 1)

  have hg0 : (lowerRamificationCard R G 0 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerRamificationCard_pos 0).ne'
  have hh0 : (lowerRamificationCard R H 0 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerRamificationCard_pos 0).ne'
  have hq0 : (lowerRamificationCard S (G ⧸ H) 0 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerRamificationCard_pos 0).ne'
  field_simp
  linear_combination (u - (m : ℚ)) * (lowerRamificationCard R H 0 : ℚ) *
      (lowerRamificationCard S (G ⧸ H) 0 : ℚ) * hcardm1 -
    (u - (m : ℚ)) * (lowerRamificationCard R H (m + 1) : ℚ) *
      (lowerRamificationCard S (G ⧸ H) (herbrandPhiCeil R H (m + 1)) : ℚ) * hcard0

theorem LowerHerbrandQuotientCompat.herbrandPhi_comp_natCast
    (hc : LowerHerbrandQuotientCompat R G S H) (n : ℕ) :
    herbrandPhi S (G ⧸ H) (herbrandPhi R H (n : ℚ)) = herbrandPhi R G (n : ℚ) := by
  induction n with
  | zero => simpa using (herbrandPhi_tower_zero (R := R) (G := G) (S := S) (H := H)).symm
  | succ m ih =>
    have hinc := hc.herbrandPhi_comp_segment m (u := (m : ℚ) + 1) (by linarith) le_rfl
    have hGseg := herbrandPhi_segment (R := R) (G := G) m
      (u := (m : ℚ) + 1) (by linarith) le_rfl
    push_cast
    linarith

theorem LowerHerbrandQuotientCompat.herbrandPhiTowerCompat
    (hc : LowerHerbrandQuotientCompat R G S H) :
    HerbrandPhiTowerCompat R G S H := by
  intro u hu
  set m := ⌊u⌋₊ with hm
  have hum : (m : ℚ) ≤ u := Nat.floor_le hu
  have hum1 : u ≤ (m : ℚ) + 1 := (Nat.lt_floor_add_one u).le
  have hGseg := herbrandPhi_segment (R := R) (G := G) m hum hum1
  have hinc := hc.herbrandPhi_comp_segment m hum hum1
  have hNat := hc.herbrandPhi_comp_natCast m
  linarith

end Tower

end IsLocalRing
p2m_reactivate "P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing"

end HerbrandPort
p2m_reactivate "P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort"

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup S (G ⧸ H) ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊)
    {u : ℚ} (hu : 0 ≤ u) :
    IsLocalRing.herbrandPhi R G u =
      IsLocalRing.herbrandPhi S (G ⧸ H) (IsLocalRing.herbrandPhi R H u) := by
  have hc : HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompat R G S H := fun n => by
    rw [HerbrandPort.IsLocalRing.herbrandPhiCeil_eq_ceil]
    exact hH n
  exact hc.herbrandPhiTowerCompat u hu

end S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
end P2MW
export P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq (solution)
