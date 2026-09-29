-- Prove2me | solution 1 for IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a0500a4f-28c0-50c9-a3b9-0c64a93655e7

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth

set_option autoImplicit false

namespace HerbrandPort

open IsLocalRing IsDiscreteValuationRing

namespace FixedPoints

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]
variable {H : Subgroup G} [H.Normal]

theorem coe_quotientMk_smul_sub_subring (g : G) (x : FixedPoints.subring R H) :
    (((QuotientGroup.mk g : G ⧸ H) • x - x : FixedPoints.subring R H) : R) =
      g • (x : R) - (x : R) :=
  rfl

end FixedPoints

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

end HerbrandPhiCeil

variable (R G) in

def LowerHerbrandQuotientCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ n : ℕ,
    (lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      lowerRamificationGroup S (G ⧸ H) (herbrandPhiCeil R H n)

variable (R G) in

def LowerHerbrandQuotientCompatCanonical (H : Subgroup G) [H.Normal]
    [IsLocalRing (FixedPoints.subring R H)] : Prop :=
  LowerHerbrandQuotientCompat R G (FixedPoints.subring R H) H

end IsLocalRing

open HerbrandPort.IsLocalRing

private theorem sum_range_succ_eq_sum_Icc_one_add {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), f i = (∑ i ∈ Finset.Icc 1 n, f i) + f 0 := by
  induction n with
  | zero =>
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, zero_add, Finset.sum_range_one, zero_add]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    exact add_right_comm _ _ _

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_sub_swap (x y : R) : addVal R (x - y) = addVal R (y - x) :=
  (addVal R).map_sub_swap x y

variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem ramificationDepth_le_addVal_smul_sub (σ : G) (x : R) :
    ramificationDepth R G σ ≤ addVal R (σ • x - x) := by
  rw [ramificationDepth_def]
  exact iInf_le _ x

theorem le_ramificationDepth {σ : G} {c : ℕ∞}
    (h : ∀ x : R, c ≤ addVal R (σ • x - x)) :
    c ≤ ramificationDepth R G σ := by
  rw [ramificationDepth_def]
  exact le_iInf h

theorem addVal_inv_smul_sub (σ : G) (x : R) :
    addVal R (σ⁻¹ • x - x) = addVal R (σ • x - x) := by
  rw [← addVal_smul σ (σ⁻¹ • x - x), smul_sub, smul_inv_smul, addVal_sub_swap]

theorem ramificationDepth_mul (σ τ : G) :
    min (ramificationDepth R G σ) (ramificationDepth R G τ) ≤
      ramificationDepth R G (σ * τ) :=
  le_ramificationDepth fun x => by
    have key : (σ * τ) • x - x = (σ • τ • x - τ • x) + (τ • x - x) := by
      rw [mul_smul, sub_add_sub_cancel]
    rw [key]
    exact le_trans (min_le_min (ramificationDepth_le_addVal_smul_sub σ (τ • x))
      (ramificationDepth_le_addVal_smul_sub τ x)) addVal_add

theorem ramificationDepth_inv (σ : G) :
    ramificationDepth R G σ⁻¹ = ramificationDepth R G σ := by
  rw [ramificationDepth_def, ramificationDepth_def]
  exact iInf_congr fun x => addVal_inv_smul_sub σ x

theorem ramificationDepth_eq_of_forall_smul_eq {H : Type*} [Group H] [MulSemiringAction H R]
    (f : H →* G) (hf : ∀ (h : H) (x : R), f h • x = h • x) (σ : H) :
    ramificationDepth R H σ = ramificationDepth R G (f σ) := by
  rw [ramificationDepth_def, ramificationDepth_def]
  exact iInf_congr fun x => by rw [hf σ x]

theorem mem_lowerRamificationGroup_iff_lt_ramificationDepth {i : ℕ} {σ : G} :
    σ ∈ lowerRamificationGroup R G i ↔ (i : ℕ∞) < ramificationDepth R G σ := by
  rw [mem_lowerRamificationGroup_iff_le_ramificationDepth,
    ENat.add_one_le_iff (ENat.coe_ne_top i)]

theorem lowerRamificationCard_eq_card_lt_ramificationDepth (i : ℕ) :
    lowerRamificationCard R G i =
      Nat.card {σ : G // (i : ℕ∞) < ramificationDepth R G σ} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    mem_lowerRamificationGroup_iff_lt_ramificationDepth)

theorem sum_lowerRamificationCard_eq_sum_toNat_min_ramificationDepth [Fintype G] (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), lowerRamificationCard R G i =
      ∑ σ : G, (min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat := by
  classical

  have key : ∀ (d : ℕ∞) (N : ℕ),
      (min d (N : ℕ∞)).toNat = ∑ i ∈ Finset.range N, if (i : ℕ∞) < d then 1 else 0 := by
    intro d N
    induction N with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, min_eq_right zero_le,
        ENat.toNat_zero]
    | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases h : (N : ℕ∞) < d
      · have h1 : ((N + 1 : ℕ) : ℕ∞) ≤ d := by
          rw [Nat.cast_add_one]
          exact (ENat.add_one_le_iff (ENat.coe_ne_top N)).mpr h
        rw [if_pos h, min_eq_right h1, min_eq_right h.le, ENat.toNat_coe, ENat.toNat_coe]
      · have hd : d ≤ (N : ℕ∞) := not_lt.mp h
        have h2 : d ≤ ((N + 1 : ℕ) : ℕ∞) := by
          rw [Nat.cast_add_one]
          exact hd.trans le_self_add
        rw [if_neg h, min_eq_left h2, min_eq_left hd, add_zero]

  have count : ∀ i : ℕ,
      (∑ σ : G, if (i : ℕ∞) < ramificationDepth R G σ then 1 else 0) =
        lowerRamificationCard R G i := by
    intro i
    rw [Finset.sum_boole, Nat.cast_id, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact (lowerRamificationCard_eq_card_lt_ramificationDepth i).symm
  calc ∑ i ∈ Finset.range (n + 1), lowerRamificationCard R G i
      = ∑ i ∈ Finset.range (n + 1), ∑ σ : G,
          if (i : ℕ∞) < ramificationDepth R G σ then 1 else 0 :=
        Finset.sum_congr rfl fun i _ => (count i).symm
    _ = ∑ σ : G, ∑ i ∈ Finset.range (n + 1),
          if (i : ℕ∞) < ramificationDepth R G σ then 1 else 0 := Finset.sum_comm
    _ = ∑ σ : G, (min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Nat.cast_add_one]
        exact (key (ramificationDepth R G σ) (n + 1)).symm

theorem lowerRamificationCard_zero_mul_herbrandPhi_natCast_add_one [Fintype G] (n : ℕ) :
    (lowerRamificationCard R G 0 : ℚ) * (herbrandPhi R G (n : ℚ) + 1) =
      ∑ σ : G, ((min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat : ℚ) := by
  have hg0 : (0 : ℚ) < (lowerRamificationCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 0)
  have hcast : ∑ i ∈ Finset.range (n + 1), (lowerRamificationCard R G i : ℚ) =
      ∑ σ : G, ((min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat : ℚ) := by
    have h := congrArg (fun k : ℕ => (k : ℚ))
      (sum_lowerRamificationCard_eq_sum_toNat_min_ramificationDepth (R := R) (G := G) n)
    push_cast at h
    exact h
  have hphi : herbrandPhi R G (n : ℚ) * (lowerRamificationCard R G 0 : ℚ) =
      ∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ) :=
    (eq_div_iff hg0.ne').mp (herbrandPhi_natCast (R := R) (G := G) n)
  calc (lowerRamificationCard R G 0 : ℚ) * (herbrandPhi R G (n : ℚ) + 1)
      = herbrandPhi R G (n : ℚ) * (lowerRamificationCard R G 0 : ℚ) +
          (lowerRamificationCard R G 0 : ℚ) := by ring
    _ = (∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ)) +
          (lowerRamificationCard R G 0 : ℚ) := by rw [hphi]
    _ = ∑ i ∈ Finset.range (n + 1), (lowerRamificationCard R G i : ℚ) :=
        (sum_range_succ_eq_sum_Icc_one_add (fun i => (lowerRamificationCard R G i : ℚ)) n).symm
    _ = ∑ σ : G, ((min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat : ℚ) := hcast

theorem ramificationDepth_mul_eq_right_of_lt {σ τ : G}
    (h : ramificationDepth R G τ < ramificationDepth R G σ) :
    ramificationDepth R G (σ * τ) = ramificationDepth R G τ := by
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    have hkey := ramificationDepth_mul (R := R) σ⁻¹ (σ * τ)
    rw [inv_mul_cancel_left, ramificationDepth_inv] at hkey
    exact absurd hkey (not_le.mpr (lt_min h hlt))
  · have hmul := ramificationDepth_mul (R := R) σ τ
    rwa [min_eq_right h.le] at hmul

variable (R G) in

noncomputable def fixedSubringRamificationDepth (H : Subgroup G) [H.Normal] (σ : G ⧸ H) :
    ℕ∞ :=
  ⨅ x : FixedPoints.subring R H, addVal R ((σ • x - x : FixedPoints.subring R H) : R)

theorem fixedSubringRamificationDepth_def (H : Subgroup G) [H.Normal] (σ : G ⧸ H) :
    fixedSubringRamificationDepth R G H σ =
      ⨅ x : FixedPoints.subring R H, addVal R ((σ • x - x : FixedPoints.subring R H) : R) :=
  rfl

theorem fixedSubringRamificationDepth_one (H : Subgroup G) [H.Normal] :
    fixedSubringRamificationDepth R G H 1 = ⊤ := by
  rw [fixedSubringRamificationDepth_def]
  simp only [one_smul, sub_self, ZeroMemClass.coe_zero, addVal_zero, iInf_top]

theorem ramificationDepth_le_fixedSubringRamificationDepth (H : Subgroup G) [H.Normal]
    (τ : G) :
    ramificationDepth R G τ ≤ fixedSubringRamificationDepth R G H (QuotientGroup.mk τ) := by
  rw [fixedSubringRamificationDepth_def]
  refine le_iInf fun x => ?_
  rw [FixedPoints.coe_quotientMk_smul_sub_subring]
  exact ramificationDepth_le_addVal_smul_sub τ (x : R)

variable (R G) in

noncomputable def cosetRamificationDepthSum (H : Subgroup G) [Fintype H] (τ₀ : G) : ℕ∞ :=
  ∑ h : H, ramificationDepth R G (τ₀ * (h : G))

theorem cosetRamificationDepthSum_def (H : Subgroup G) [Fintype H] (τ₀ : G) :
    cosetRamificationDepthSum R G H τ₀ =
      ∑ h : H, ramificationDepth R G (τ₀ * (h : G)) :=
  rfl

theorem ramificationDepth_subgroup_coe {H : Subgroup G} (h : H) :
    ramificationDepth R H h = ramificationDepth R G (h : G) :=
  ramificationDepth_eq_of_forall_smul_eq H.subtype (fun _ _ => rfl) h

theorem cosetRamificationDepthSum_eq_top_of_mem {H : Subgroup G} [Fintype H] {τ₀ : G}
    (h : τ₀ ∈ H) :
    cosetRamificationDepthSum R G H τ₀ = ⊤ := by
  rw [cosetRamificationDepthSum_def, ENat.sum_eq_top]
  refine ⟨⟨τ₀⁻¹, H.inv_mem h⟩, Finset.mem_univ _, ?_⟩
  show ramificationDepth R G (τ₀ * τ₀⁻¹) = ⊤
  rw [mul_inv_cancel]
  exact ramificationDepth_one

theorem cosetRamificationDepthSum_ne_top {H : Subgroup G} [H.Normal] [Fintype H]
    [FaithfulSMul G R] {τ₀ : G} (h : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1) :
    cosetRamificationDepthSum R G H τ₀ ≠ ⊤ := by
  rw [cosetRamificationDepthSum_def]
  intro htop
  rw [ENat.sum_eq_top] at htop
  obtain ⟨h', -, hh'⟩ := htop
  refine h ?_
  rw [QuotientGroup.eq_one_iff]
  have h1 : τ₀ * (h' : G) = 1 := by
    have := ramificationDepth_eq_top_iff (R := R) (G := G) (σ := τ₀ * (h' : G))
    exact this.mp hh'
  rw [eq_inv_of_mul_eq_one_left h1]
  exact H.inv_mem h'.2

theorem ramificationDepth_mul_coe_eq_min {H : Subgroup G} {τ₀ : G}
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀)
    (h : H) :
    ramificationDepth R G (τ₀ * (h : G)) =
      min (ramificationDepth R G (h : G)) (ramificationDepth R G τ₀) := by
  rcases lt_or_ge (ramificationDepth R G (h : G)) (ramificationDepth R G τ₀) with hlt | hge
  · rw [min_eq_left hlt.le]
    exact ramificationDepth_mul_eq_right_of_lt hlt
  · rw [min_eq_right hge]
    refine le_antisymm (hmax h) ?_
    have hmul := ramificationDepth_mul (R := R) τ₀ (h : G)
    rwa [min_eq_left hge] at hmul

theorem exists_max_ramificationDepth_coset {H : Subgroup G} [Finite H] (τ₀ : G) :
    ∃ h₀ : H, ∀ h : H,
      ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G (τ₀ * (h₀ : G)) := by
  haveI : Nonempty H := ⟨1⟩
  exact Finite.exists_max fun h : H => ramificationDepth R G (τ₀ * (h : G))

theorem exists_quotientMk_eq_max_ramificationDepth {H : Subgroup G} [Finite H] (τ₀ : G) :
    ∃ τ₁ : G, (QuotientGroup.mk τ₁ : G ⧸ H) = QuotientGroup.mk τ₀ ∧
      ∀ h : H, ramificationDepth R G (τ₁ * (h : G)) ≤ ramificationDepth R G τ₁ := by
  obtain ⟨h₀, hh₀⟩ := exists_max_ramificationDepth_coset (R := R) (H := H) τ₀
  refine ⟨τ₀ * (h₀ : G), QuotientGroup.mk_mul_of_mem τ₀ h₀.2, fun h => ?_⟩
  have hassoc : (τ₀ * (h₀ : G)) * (h : G) = τ₀ * ((h₀ * h : H) : G) := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hassoc]
  exact hh₀ (h₀ * h)

theorem sum_toNat_ramificationDepth_coset_eq {H : Subgroup G} [Fintype H] {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ∑ h : H, ((ramificationDepth R G (τ₀ * (h : G))).toNat : ℚ) =
      (lowerRamificationCard R H 0 : ℚ) * (herbrandPhi R H (n : ℚ) + 1) := by
  have hbridge : (lowerRamificationCard R H 0 : ℚ) * (herbrandPhi R H (n : ℚ) + 1) =
      ∑ h : H, ((min (ramificationDepth R H h) ((n : ℕ∞) + 1)).toNat : ℚ) :=
    lowerRamificationCard_zero_mul_herbrandPhi_natCast_add_one n
  rw [hbridge]
  refine Finset.sum_congr rfl fun h _ => ?_
  have key : ramificationDepth R G (τ₀ * (h : G)) =
      min (ramificationDepth R H h) ((n : ℕ∞) + 1) := by
    rw [ramificationDepth_mul_coe_eq_min hmax h, hτ₀, ramificationDepth_subgroup_coe h]
  rw [key]

theorem cosetRamificationDepthSum_toNat_eq {H : Subgroup G} [Fintype H] {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ((cosetRamificationDepthSum R G H τ₀).toNat : ℚ) =
      (lowerRamificationCard R H 0 : ℚ) * (herbrandPhi R H (n : ℚ) + 1) := by
  have hne : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≠ ⊤ := by
    intro h
    refine ne_top_of_le_ne_top ?_ (hmax h)
    rw [hτ₀, ← Nat.cast_add_one]
    exact ENat.coe_ne_top _
  rw [cosetRamificationDepthSum_def, ENat.toNat_sum (fun h _ => hne h)]
  push_cast
  exact sum_toNat_ramificationDepth_coset_eq hτ₀ hmax

theorem cosetRamificationDepthSum_eq_zero_of_eq_zero {H : Subgroup G} [Fintype H] {τ₀ : G}
    (hτ₀ : ramificationDepth R G τ₀ = 0)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    cosetRamificationDepthSum R G H τ₀ = 0 := by
  rw [cosetRamificationDepthSum_def]
  refine Finset.sum_eq_zero fun h _ => ?_
  exact le_antisymm (hτ₀ ▸ hmax h) zero_le

variable (R G) in

def RamificationDepthCosetLemma (H : Subgroup G) [H.Normal] [Fintype H] : Prop :=
  ∀ τ₀ : G,
    fixedSubringRamificationDepth R G H (QuotientGroup.mk τ₀) =
      cosetRamificationDepthSum R G H τ₀

namespace RamificationDepthCosetLemma

theorem fixedSubringRamificationDepth_ne_top {H : Subgroup G} [H.Normal] [Fintype H]
    [FaithfulSMul G R] (hc : RamificationDepthCosetLemma R G H) {τ₀ : G}
    (h : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1) :
    fixedSubringRamificationDepth R G H (QuotientGroup.mk τ₀) ≠ ⊤ := by
  rw [hc τ₀]
  exact cosetRamificationDepthSum_ne_top h

theorem toNat_fixedSubringRamificationDepth_eq {H : Subgroup G} [H.Normal] [Fintype H]
    (hc : RamificationDepthCosetLemma R G H) {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ((fixedSubringRamificationDepth R G H (QuotientGroup.mk τ₀)).toNat : ℚ) =
      (lowerRamificationCard R H 0 : ℚ) * (herbrandPhi R H (n : ℚ) + 1) := by
  rw [hc τ₀]
  exact cosetRamificationDepthSum_toNat_eq hτ₀ hmax

end RamificationDepthCosetLemma

section SerreDisplay

variable {H : Subgroup G} [H.Normal]
variable [IsDiscreteValuationRing (FixedPoints.subring R H)]

theorem fixedSubringRamificationDepth_eq_mul_ramificationDepth {e : ℕ}
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (e : ℕ∞) * addVal (FixedPoints.subring R H) y)
    (σ : G ⧸ H) :
    fixedSubringRamificationDepth R G H σ =
      (e : ℕ∞) * ramificationDepth (FixedPoints.subring R H) (G ⧸ H) σ := by
  haveI : Nonempty (FixedPoints.subring R H) := ⟨0⟩
  rw [fixedSubringRamificationDepth_def, ramificationDepth_def, ENat.mul_iInf]
  exact iInf_congr fun x => hscale _

theorem RamificationDepthCosetLemma.mul_ramificationDepth_eq_cosetSum [Fintype H] {e : ℕ}
    (hc : RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (e : ℕ∞) * addVal (FixedPoints.subring R H) y)
    (τ₀ : G) :
    (e : ℕ∞) * ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) =
      cosetRamificationDepthSum R G H τ₀ := by
  rw [← fixedSubringRamificationDepth_eq_mul_ramificationDepth hscale]
  exact hc τ₀

theorem RamificationDepthCosetLemma.toNat_ramificationDepth_quotient_eq [Fintype H] {e : ℕ}
    (hc : RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (e : ℕ∞) * addVal (FixedPoints.subring R H) y)
    (he : e = lowerRamificationCard R H 0) {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ((ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀)).toNat : ℚ) =
      herbrandPhi R H (n : ℚ) + 1 := by
  have hpos : 0 < lowerRamificationCard R H 0 := lowerRamificationCard_pos 0
  have he0 : (lowerRamificationCard R H 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hsum := cosetRamificationDepthSum_toNat_eq (H := H) hτ₀ hmax
  rw [← hc.mul_ramificationDepth_eq_cosetSum hscale τ₀, ENat.toNat_mul] at hsum
  have hcoe : ((e : ℕ∞)).toNat = e := by simp
  rw [hcoe] at hsum
  push_cast at hsum
  rw [he] at hsum
  exact mul_left_cancel₀ he0 hsum

end SerreDisplay

section FromCosetLemma

variable {H : Subgroup G} [H.Normal] [Fintype H]

theorem mem_lowerRamificationGroup_map_iff_max_depth {τ₀ : G} {n : ℕ}
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    (QuotientGroup.mk τ₀ : G ⧸ H) ∈
        (lowerRamificationGroup R G n).map (QuotientGroup.mk' H) ↔
      (n : ℕ∞) + 1 ≤ ramificationDepth R G τ₀ := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσn, hσcls⟩
    have hh : τ₀⁻¹ * σ ∈ H :=
      QuotientGroup.eq.mp ((QuotientGroup.mk'_apply H σ ▸ hσcls).symm)
    have hσeq : σ = τ₀ * (τ₀⁻¹ * σ) := by group
    exact le_trans (mem_lowerRamificationGroup_iff_le_ramificationDepth.mp hσn)
      (hσeq ▸ hmax ⟨τ₀⁻¹ * σ, hh⟩)
  · intro hle
    exact ⟨τ₀, mem_lowerRamificationGroup_iff_le_ramificationDepth.mpr hle, rfl⟩

section SerreDisplay

variable [FaithfulSMul G R] [IsDiscreteValuationRing (FixedPoints.subring R H)]

namespace RamificationDepthCosetLemma

theorem ramificationDepth_quotient_ne_top (hc : RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerRamificationCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y)
    {τ₀ : G} (hne : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1) :
    ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) ≠ ⊤ := by
  have hfix := hc.fixedSubringRamificationDepth_ne_top hne
  rw [fixedSubringRamificationDepth_eq_mul_ramificationDepth hscale] at hfix
  intro habs
  refine hfix ?_
  rw [habs, ENat.mul_top]
  exact_mod_cast (lowerRamificationCard_pos (R := R) (G := H) 0).ne'

theorem ramificationDepth_quotient_eq_zero (hc : RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerRamificationCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y)
    {τ₀ : G} (hτ₀ : ramificationDepth R G τ₀ = 0)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) = 0 := by
  have hfix := (fixedSubringRamificationDepth_eq_mul_ramificationDepth hscale
    (QuotientGroup.mk τ₀)).symm.trans
    ((hc τ₀).trans (cosetRamificationDepthSum_eq_zero_of_eq_zero hτ₀ hmax))
  rcases mul_eq_zero.mp hfix with h | h
  · exact absurd h (by exact_mod_cast (lowerRamificationCard_pos (R := R) (G := H) 0).ne')
  · exact h

theorem depth_iff_depth (hc : RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerRamificationCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y)
    {τ₀ : G} (hne : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀)
    (n : ℕ) :
    (n : ℕ∞) + 1 ≤ ramificationDepth R G τ₀ ↔
      (herbrandPhiCeil R H n : ℕ∞) + 1 ≤
        ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) := by

  have hτ₀fin : ramificationDepth R G τ₀ ≠ ⊤ := fun habs =>
    hne (by rw [ramificationDepth_eq_top_iff.mp habs]; exact QuotientGroup.mk_one H)
  have hqfin := hc.ramificationDepth_quotient_ne_top hscale hne
  set d := (ramificationDepth R G τ₀).toNat with hddef
  set k := (ramificationDepth (FixedPoints.subring R H) (G ⧸ H)
    (QuotientGroup.mk τ₀)).toNat with hkdef

  rw [← ENat.coe_toNat hτ₀fin, ← ENat.coe_toNat hqfin, ← hddef, ← hkdef,
    show ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) from by push_cast; ring,
    show ((herbrandPhiCeil R H n : ℕ∞) + 1) =
      ((herbrandPhiCeil R H n + 1 : ℕ) : ℕ∞) from by push_cast; ring,
    Nat.cast_le, Nat.cast_le]

  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  ·
    have hτ₀ : ramificationDepth R G τ₀ = 0 := by
      rw [← ENat.coe_toNat hτ₀fin, ← hddef, hd0, Nat.cast_zero]
    have hk0 : k = 0 := by
      rw [hkdef, hc.ramificationDepth_quotient_eq_zero hscale hτ₀ hmax]; rfl
    simp [hd0, hk0]
  ·
    obtain ⟨m, hmd⟩ : ∃ m, d = m + 1 := ⟨d - 1, (Nat.sub_add_cancel hdpos).symm⟩
    have hm : ramificationDepth R G τ₀ = (m : ℕ∞) + 1 := by
      rw [← ENat.coe_toNat hτ₀fin, ← hddef, hmd]; push_cast; ring
    have hlemme5 := hc.toNat_ramificationDepth_quotient_eq hscale rfl hm hmax
    rw [← hkdef] at hlemme5
    have hk1 : 1 ≤ k := by
      have : (1 : ℚ) ≤ (k : ℚ) := by
        rw [hlemme5]; linarith [herbrandPhi_nonneg (R := R) (G := H) (Nat.cast_nonneg m)]
      exact_mod_cast this
    have hφm : herbrandPhi R H (m : ℚ) = ((k - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub hk1, hlemme5]; ring
    rw [hmd, herbrandPhiCeil_eq_ceil, ← Nat.le_sub_iff_add_le hk1,
      Nat.ceil_le, ← hφm,
      (herbrandPhi_strictMono (R := R) (G := H)).le_iff_le, Nat.cast_le]
    omega

end RamificationDepthCosetLemma

theorem lowerHerbrandQuotientCompatCanonical_of_cosetLemma
    (hc : RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerRamificationCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y) :
    LowerHerbrandQuotientCompatCanonical R G H := by
  intro n
  ext σ
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective σ
  by_cases hne : (QuotientGroup.mk τ : G ⧸ H) = 1
  · rw [hne]; exact iff_of_true (Subgroup.one_mem _) (Subgroup.one_mem _)
  · obtain ⟨τ₀, hcls, hmax⟩ :=
      exists_quotientMk_eq_max_ramificationDepth (R := R) (H := H) τ
    rw [← hcls, mem_lowerRamificationGroup_map_iff_max_depth hmax,
      mem_lowerRamificationGroup_iff_le_ramificationDepth]
    exact hc.depth_iff_depth hscale (hcls ▸ hne) hmax n

end SerreDisplay

end FromCosetLemma

end IsDiscreteValuationRing

end HerbrandPort

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {H : Subgroup G} [H.Normal] [Fintype H] [IsDiscreteValuationRing (FixedPoints.subring R H)]
    (hH : ∀ τ : G,
      (⨅ z : FixedPoints.subring R H,
          IsDiscreteValuationRing.addVal R
            (((QuotientGroup.mk τ : G ⧸ H) • z - z : FixedPoints.subring R H) : R)) =
        ∑ h : H, IsDiscreteValuationRing.ramificationDepth R G (τ * (h : G)))
    (he : ∀ z : FixedPoints.subring R H,
      IsDiscreteValuationRing.addVal R (z : R) =
        (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
          IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z)
    (n : ℕ) :
    (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊ := by
  have h := HerbrandPort.IsDiscreteValuationRing.lowerHerbrandQuotientCompatCanonical_of_cosetLemma
    (R := R) (G := G) (H := H) hH he n
  rwa [HerbrandPort.IsLocalRing.herbrandPhiCeil_eq_ceil] at h

end S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
end P2MW
export P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth (solution)
