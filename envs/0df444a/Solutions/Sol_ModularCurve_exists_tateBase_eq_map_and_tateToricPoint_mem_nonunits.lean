-- Prove2me | solution 1 for ModularCurve.exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/001a7a74-695b-50cc-9562-842f463baa1e

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_ModularCurve_coeff_tateToricPoint_mem_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits

namespace TateWAux

open ModularCurve

noncomputable def expandPS {R : Type*} [CommRing R] (p : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) f else 0

theorem coeff_expandPS {R : Type*} [CommRing R] (p : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (expandPS p f) = if p ∣ n then PowerSeries.coeff (n / p) f else 0 :=
  PowerSeries.coeff_mk _ _

theorem expandPS_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (p : ℕ) (f : PowerSeries R) :
    (expandPS p f).map g = expandPS p (f.map g) := by
  ext n; simp only [PowerSeries.coeff_map, coeff_expandPS]; split_ifs <;> simp

theorem qExpand_ofPowerSeries {R : Type*} [CommRing R] (p : ℕ) [NeZero p] (f : PowerSeries R) :
    qExpand R p (HahnSeries.ofPowerSeries ℤ R f) = HahnSeries.ofPowerSeries ℤ R (expandPS p f) := by
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul]
    rcases le_or_gt 0 m with hm | hm
    · lift m to ℕ using hm with m
      rw [show ((p : ℤ) * (m : ℤ)) = ((p * m : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, coeff_expandPS,
        if_pos (Dvd.intro m rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne p))]
    · rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg]
      have : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
      nlinarith
  · rw [qExpand_coeff_of_not_dvd _ _ hk]
    rcases le_or_gt 0 k with hk0 | hk0
    · lift k to ℕ using hk0 with k
      rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_expandPS, if_neg]
      intro h; exact hk (by exact_mod_cast h)
    · rw [ofPowerSeries_coeff_of_neg _ hk0]

theorem coeff_tateΔ : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 ∧ PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
  have hΔeq : tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 - PowerSeries.C 432 * tateA6 ^ 2
        + PowerSeries.C 72 * (tateA4 * tateA6) := by
    rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
      show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
      show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
      tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  have hc0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_tateA4, constantCoeff_tateA6]
    ring
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  have hc1 : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
      coeff_one_tateA6]
    norm_num
  exact ⟨hc0, hc1⟩

theorem qExpand_laurentOfInt {L : Type} [Field L] (A₀ : ValuationSubring L) (p : ℕ) [NeZero p] (f : PowerSeries ℤ) :
    qExpand L p (laurentOfInt L f) =
      HahnSeries.ofPowerSeries ℤ L ((expandPS p (f.map (Int.castRingHom ↥A₀))).map (algebraMap ↥A₀ L)) := by
  rw [laurentOfInt_apply, qExpand_ofPowerSeries, expandPS_map]
  congr 2

end TateWAux

open ModularCurve TateWAux in
set_option maxHeartbeats 8000000 in
theorem solution
    (L : Type) [Field L] (A₀ : ValuationSubring L)
    (L₂ : Subfield (LaurentSeries L)) (W₂ : ValuationSubring ↥L₂)
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (hW₂ : ∀ f : ↥L₂, f ∈ W₂ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (hW₂' : ∀ f : ↥L₂, f ∈ W₂.nonunits ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      x.map (IsLocalRing.residue ↥A₀) = 0 ∧
      ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (p : ℕ) [NeZero p] (c : (↥A₀)ˣ) (hc : 1 - (c : ↥A₀) ∈ IsLocalRing.maximalIdeal ↥A₀) (hc1 : ((c : ↥A₀) : L) ≠ 1) :

    (∃ T : WeierstrassCurve ↥W₂,
      (T.map W₂.subtype).map L₂.subtype = ModularCurve.tateBase L p ∧
      (T.map (IsLocalRing.residue ↥W₂)).Δ ≠ 0) ∧

    (∃ xt yt : ↥L₂,
      ((xt : ↥L₂) : LaurentSeries L) = (ModularCurve.tateToricPoint L p (Units.map (A₀.subtype : ↥A₀ →* L) c)).1 ∧
      ((yt : ↥L₂) : LaurentSeries L) = (ModularCurve.tateToricPoint L p (Units.map (A₀.subtype : ↥A₀ →* L) c)).2 ∧
      yt ≠ 0 ∧ xt / yt ∈ W₂.nonunits ∧ yt⁻¹ ∈ W₂.nonunits) := by
  classical

  obtain ⟨S, hS⟩ : ∃ S : PowerSeries ↥A₀ →+* LaurentSeries L,
      ∀ x, S x = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)) :=
    ⟨(HahnSeries.ofPowerSeries ℤ L).comp (PowerSeries.map (algebraMap ↥A₀ L)), fun _ => rfl⟩
  have hSinj : Function.Injective S := by
    intro x y h
    rw [hS, hS] at h
    have h' := HahnSeries.ofPowerSeries_injective h
    exact PowerSeries.map_injective (algebraMap ↥A₀ L) Subtype.val_injective h'
  have hSC : ∀ a : ↥A₀, S (PowerSeries.C a) = HahnSeries.C ((a : ↥A₀) : L) := by
    intro a; rw [hS, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]; rfl
  have hS1 : S 1 = 1 := map_one S
  haveI : Nontrivial (IsLocalRing.ResidueField ↥A₀) := inferInstance

  have hcoef : ∀ f : PowerSeries ℤ, ∃ x : PowerSeries ↥A₀, qExpand L p (laurentOfInt L f) = S x ∧
      ∀ n, PowerSeries.coeff n x = if p ∣ n then ((PowerSeries.coeff (n / p) f : ℤ) : ↥A₀) else 0 := by
    intro f
    refine ⟨expandPS p (f.map (Int.castRingHom ↥A₀)), by rw [hS]; exact qExpand_laurentOfInt A₀ p f, fun n => ?_⟩
    rw [coeff_expandPS]; split_ifs <;> simp
  obtain ⟨a4, ha4, -⟩ := hcoef tateA4
  obtain ⟨a6, ha6, -⟩ := hcoef tateA6
  obtain ⟨δ, hδ, hδc⟩ := hcoef tatePowerSeries.Δ
  have hB4 : (tateBase L p).a₄ = S a4 := by rw [← ha4]; rfl
  have hB6 : (tateBase L p).a₆ = S a6 := by rw [← ha6]; rfl
  have hB1 : (tateBase L p).a₁ = 1 := by simp [tateBase, tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  have hB2 : (tateBase L p).a₂ = 0 := by simp [tateBase, tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  have hB3 : (tateBase L p).a₃ = 0 := by simp [tateBase, tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  have hBΔ : (tateBase L p).Δ = S δ := by
    rw [← hδ, tateBase, WeierstrassCurve.map_Δ, tateLaurent, WeierstrassCurve.map_Δ]
  have memL : ∀ x : PowerSeries ↥A₀, S x ∈ L₂ := fun x =>
    (hL₂ _).mpr ⟨x, 1, one_ne_zero, by rw [map_one, map_one, mul_one, ← hS]⟩
  have memW : ∀ x : PowerSeries ↥A₀, (⟨S x, memL x⟩ : ↥L₂) ∈ W₂ := fun x =>
    (hW₂ _).mpr ⟨x, 1, by rw [map_one]; exact one_ne_zero, by
      show S x * _ = _; rw [map_one, map_one, mul_one, ← hS]⟩
  refine ⟨⟨⟨1, 0, 0, ⟨⟨S a4, memL a4⟩, memW a4⟩, ⟨⟨S a6, memL a6⟩, memW a6⟩⟩, ?_, ?_⟩, ?_⟩
  · ext
    · simp [WeierstrassCurve.map, hB1]
    · simp [WeierstrassCurve.map, hB2]
    · simp [WeierstrassCurve.map, hB3]
    · simp [WeierstrassCurve.map, hB4]
    · simp [WeierstrassCurve.map, hB6]
  ·
    intro hzero
    rw [WeierstrassCurve.map_Δ, IsLocalRing.residue_eq_zero_iff] at hzero
    have hnu : ((WeierstrassCurve.Δ ⟨1, 0, 0, ⟨⟨S a4, memL a4⟩, memW a4⟩, ⟨⟨S a6, memL a6⟩, memW a6⟩⟩ : ↥W₂) : ↥L₂) ∈ W₂.nonunits :=
      ValuationSubring.coe_mem_nonunits_iff.mpr hzero
    obtain ⟨x, y, hy, hx, hxy⟩ := (hW₂' _).mp hnu
    have hΔcoe : (((WeierstrassCurve.Δ ⟨1, 0, 0, ⟨⟨S a4, memL a4⟩, memW a4⟩, ⟨⟨S a6, memL a6⟩, memW a6⟩⟩ : ↥W₂) : ↥L₂) : LaurentSeries L) = S δ := by
      rw [← hBΔ]
      have e1 := WeierstrassCurve.map_Δ (⟨1, 0, 0, ⟨⟨S a4, memL a4⟩, memW a4⟩, ⟨⟨S a6, memL a6⟩, memW a6⟩⟩ : WeierstrassCurve ↥W₂) W₂.subtype
      have e2 := WeierstrassCurve.map_Δ ((⟨1, 0, 0, ⟨⟨S a4, memL a4⟩, memW a4⟩, ⟨⟨S a6, memL a6⟩, memW a6⟩⟩ : WeierstrassCurve ↥W₂).map W₂.subtype) L₂.subtype
      have e3 : ((⟨1, 0, 0, ⟨⟨S a4, memL a4⟩, memW a4⟩, ⟨⟨S a6, memL a6⟩, memW a6⟩⟩ : WeierstrassCurve ↥W₂).map W₂.subtype).map L₂.subtype = tateBase L p := by
        ext
        · simp [WeierstrassCurve.map, hB1]
        · simp [WeierstrassCurve.map, hB2]
        · simp [WeierstrassCurve.map, hB3]
        · simp [WeierstrassCurve.map, hB4]
        · simp [WeierstrassCurve.map, hB6]
      rw [← e3, e2, e1]; rfl
    rw [hΔcoe, ← hS y, ← hS x, ← map_mul] at hxy
    have hxy' := hSinj hxy
    have hred := congrArg (PowerSeries.map (IsLocalRing.residue ↥A₀)) hxy'
    rw [map_mul, hx, mul_eq_zero] at hred
    rcases hred with h1 | h1
    ·
      have := congrArg (PowerSeries.coeff p) h1
      rw [PowerSeries.coeff_map, hδc, if_pos (dvd_refl p), Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne p)),
        coeff_tateΔ.2, map_zero] at this
      simp at this
    · exact hy h1
  ·
    obtain ⟨cL, hcL⟩ : ∃ cL : Lˣ, cL = Units.map (A₀.subtype : ↥A₀ →* L) c := ⟨_, rfl⟩
    have hcLv : (cL : L) = ((c : ↥A₀) : L) := by rw [hcL]; rfl
    have hcLi : ((cL⁻¹ : Lˣ) : L) = (((c⁻¹ : (↥A₀)ˣ) : ↥A₀) : L) := by rw [hcL, ← map_inv]; rfl
    obtain ⟨hpos, h0x, h0y, hneg⟩ := ModularCurve.coeff_tateToricPoint_mem_of_mem L p A₀.toSubring cL
      (by rw [hcLv]; exact (c : ↥A₀).2) (by rw [hcLi]; exact ((c⁻¹ : (↥A₀)ˣ) : ↥A₀).2)
    obtain ⟨pt, hpt⟩ : ∃ pt, pt = ModularCurve.tateToricPoint L p cL := ⟨_, rfl⟩
    rw [← hpt] at hpos h0x h0y hneg
    obtain ⟨a, ha⟩ : ∃ a : ↥A₀, a = 1 - (c : ↥A₀) := ⟨_, rfl⟩
    have ha𝔪 : a ∈ IsLocalRing.maximalIdeal ↥A₀ := ha ▸ hc
    have haL : (a : L) = 1 - (cL : L) := by rw [ha, hcLv]; rfl
    have ha0 : (a : L) ≠ 0 := by rw [haL, sub_ne_zero]; exact fun h => hc1 (hcLv ▸ h.symm)
    have ha0' : a ≠ 0 := fun h => ha0 (by rw [h]; rfl)
    have hinv : Ring.inverse (1 - (cL : L)) = (a : L)⁻¹ := by rw [← haL, Ring.inverse_eq_inv']
    have hc0 : (cL : L) ≠ 0 := cL.ne_zero

    obtain ⟨Xs, hXs⟩ : ∃ g : PowerSeries L, pt.1 = HahnSeries.ofPowerSeries ℤ L g := ⟨_, by rw [hpt]; exact ModularCurve.tateToricPoint_fst L p cL⟩
    obtain ⟨Ys, hYs⟩ : ∃ g : PowerSeries L, pt.2 = HahnSeries.ofPowerSeries ℤ L g := ⟨_, by rw [hpt]; exact ModularCurve.tateToricPoint_snd L p cL⟩
    have hXc : ∀ m : ℕ, pt.1.coeff (m : ℤ) = PowerSeries.coeff m Xs := fun m => by rw [hXs, HahnSeries.ofPowerSeries_apply_coeff]
    have hYc : ∀ m : ℕ, pt.2.coeff (m : ℤ) = PowerSeries.coeff m Ys := fun m => by rw [hYs, HahnSeries.ofPowerSeries_apply_coeff]

    have memX : ∀ m : ℕ, m ≠ 0 → PowerSeries.coeff m Xs ∈ A₀ := fun m hm => by
      rw [← hXc]; exact (hpos m (Nat.pos_of_ne_zero hm)).1
    have memY : ∀ m : ℕ, m ≠ 0 → PowerSeries.coeff m Ys ∈ A₀ := fun m hm => by
      rw [← hYc]; exact (hpos m (Nat.pos_of_ne_zero hm)).2
    let Xt : PowerSeries ↥A₀ := PowerSeries.mk fun m => if hm : m = 0 then (c : ↥A₀) else a ^ 2 * ⟨PowerSeries.coeff m Xs, memX m hm⟩
    let Yt : PowerSeries ↥A₀ := PowerSeries.mk fun m => if hm : m = 0 then (c : ↥A₀) ^ 2 else a ^ 3 * ⟨PowerSeries.coeff m Ys, memY m hm⟩
    have hX0 : PowerSeries.coeff 0 Xs = (cL : L) * ((a : ↥A₀) : L)⁻¹ ^ 2 := by
      rw [← hinv, ← h0x, ← hXc 0]; rfl
    have hY0 : PowerSeries.coeff 0 Ys = (cL : L) ^ 2 * ((a : ↥A₀) : L)⁻¹ ^ 3 := by
      rw [← hinv, ← h0y, ← hYc 0]; rfl
    have hXt : pt.1 * S (PowerSeries.C (a ^ 2)) = S Xt := by
      rw [hSC, hS, hXs, ← HahnSeries.ofPowerSeries_C, ← map_mul]
      congr 1
      ext m
      rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_map, PowerSeries.coeff_mk]
      by_cases hm : m = 0
      · subst hm
        rw [dif_pos rfl, hX0]
        show _ = ((c : ↥A₀) : L)
        rw [← hcLv]
        push_cast
        field_simp
      · rw [dif_neg hm]
        show _ = ((a ^ 2 * ⟨PowerSeries.coeff m Xs, memX m hm⟩ : ↥A₀) : L)
        push_cast
        ring
    have hYt : pt.2 * S (PowerSeries.C (a ^ 3)) = S Yt := by
      rw [hSC, hS, hYs, ← HahnSeries.ofPowerSeries_C, ← map_mul]
      congr 1
      ext m
      rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_map, PowerSeries.coeff_mk]
      by_cases hm : m = 0
      · subst hm
        rw [dif_pos rfl, hY0]
        show _ = (((c : ↥A₀) ^ 2 : ↥A₀) : L)
        push_cast
        rw [← hcLv]
        field_simp
      · rw [dif_neg hm]
        show _ = ((a ^ 3 * ⟨PowerSeries.coeff m Ys, memY m hm⟩ : ↥A₀) : L)
        push_cast
        ring
    have hres_c : IsLocalRing.residue ↥A₀ (c : ↥A₀) ≠ 0 := by
      intro h0
      rw [IsLocalRing.residue_eq_zero_iff] at h0
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp h0) c.isUnit
    have hres_a : IsLocalRing.residue ↥A₀ a = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr ha𝔪
    have hYbar : Yt.map (IsLocalRing.residue ↥A₀) ≠ 0 := by
      intro h
      have := congrArg (PowerSeries.coeff 0) h
      rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, dif_pos rfl, map_zero, map_pow] at this
      exact pow_ne_zero 2 hres_c this
    have hy0 : pt.2 ≠ 0 := by
      intro h
      have := hYc 0
      rw [h, hY0] at this
      exact (mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 3 (inv_ne_zero ha0))) (by simpa using this.symm)

    have hxL : pt.1 ∈ L₂ := (hL₂ _).mpr ⟨Xt, PowerSeries.C (a ^ 2), by
      rw [Ne, PowerSeries.ext_iff, not_forall]; exact ⟨0, by simp [pow_ne_zero 2 ha0']⟩, by simpa only [hS] using hXt⟩
    have hyL : pt.2 ∈ L₂ := (hL₂ _).mpr ⟨Yt, PowerSeries.C (a ^ 3), by
      rw [Ne, PowerSeries.ext_iff, not_forall]; exact ⟨0, by simp [pow_ne_zero 3 ha0']⟩, by simpa only [hS] using hYt⟩
    refine ⟨⟨pt.1, hxL⟩, ⟨pt.2, hyL⟩, by show pt.1 = _; rw [hpt, hcL], by show pt.2 = _; rw [hpt, hcL], fun h => hy0 (congrArg Subtype.val h), ?_, ?_⟩
    ·
      refine (hW₂' _).mpr ⟨PowerSeries.C a * Xt, Yt, hYbar, by rw [map_mul, PowerSeries.map_C, hres_a, map_zero, zero_mul], ?_⟩
      have hC3 : PowerSeries.C (a ^ 3) = PowerSeries.C a * PowerSeries.C (a ^ 2) := by rw [← map_mul, ← pow_succ']
      rw [Subfield.coe_div]
      show pt.1 / pt.2 * _ = _
      rw [← hS, ← hS, ← hYt, map_mul S, ← hXt, hC3, map_mul S]
      field_simp
    ·
      refine (hW₂' _).mpr ⟨PowerSeries.C (a ^ 3), Yt, hYbar, by rw [PowerSeries.map_C, map_pow, hres_a, zero_pow three_ne_zero, map_zero], ?_⟩
      rw [Subfield.coe_inv]
      show pt.2⁻¹ * _ = _
      rw [← hS, ← hYt, ← mul_assoc, inv_mul_cancel₀ hy0, one_mul]
      exact hS _

end S_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits
end P2MW
export P2MW.S_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits (solution)
