-- Prove2me | solution 1 for ModularCurve.qTwist_nonToricPoint_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7040ee74-09a5-5110-a352-1894ae2dfc46

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open ModularCurve

namespace P2MKcQTwistSlot

universe u

variable {K : Type u} [CommRing K]

theorem qTwist_ofPowerSeries (u : Kˣ) (f : PowerSeries K) :
    qTwist u (HahnSeries.ofPowerSeries ℤ K f) =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.rescale (u : K) f) := by
  ext k
  rw [qTwist_coeff]
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_rescale, zpow_natCast, Units.val_pow_eq_pow_val]
  · have h0 : ∀ g : PowerSeries K, (HahnSeries.ofPowerSeries ℤ K g).coeff k = 0 := by
      intro g
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_notin_range
      rintro ⟨n, hn⟩
      have : (0 : ℤ) ≤ k := by rw [← hn]; exact Int.natCast_nonneg n
      omega
    rw [h0, h0, mul_zero]

theorem zeta_pow_of_eq {M : ℕ} (ζ : Kˣ) (hζ : ζ ^ M = 1) {n m t : ℕ} (h : n = M * m + t) :
    (ζ : K) ^ n = (ζ : K) ^ t := by
  rw [h, pow_add, pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hζ, one_pow,
    Units.val_one, one_mul]

theorem zeta_pow_mul_of_add_eq {M : ℕ} (ζ : Kˣ) (hζ : ζ ^ M = 1) {n m t : ℕ} (h : n + t = M * m) :
    (ζ : K) ^ n * (ζ : K) ^ t = 1 := by
  rw [← pow_add, h, pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hζ, one_pow,
    Units.val_one]

theorem val_mul_pow_pow (c ζ : Kˣ) (j e : ℕ) :
    ((c * ζ ^ j : Kˣ) : K) ^ e = (c : K) ^ e * (ζ : K) ^ (j * e) := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]

theorem val_inv_mul_pow_pow (c ζ : Kˣ) (j e : ℕ) :
    (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e * (ζ : K) ^ (j * e) = ((c⁻¹ : Kˣ) : K) ^ e := by
  have h : ((c * ζ ^ j)⁻¹ : Kˣ) ^ e * ζ ^ (j * e) = c⁻¹ ^ e := by
    rw [mul_inv, mul_pow, inv_pow (ζ ^ j), ← pow_mul, mul_assoc, inv_mul_cancel, mul_one]
  have h' := congrArg Units.val h
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val] at h'
  exact h'

theorem term_twist {M : ℕ} (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ) (j n m e : ℕ) (hj : 0 < j)
    (α β γ : K) :
    (ζ : K) ^ n * (α * (if n = M * m + j * e then (c : K) ^ e else 0) +
        β * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        γ * (if n = M * m then 1 else 0)) =
      α * (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) +
        β * (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        γ * (if n = M * m then 1 else 0) := by
  have S1 : (ζ : K) ^ n * (if n = M * m + j * e then (c : K) ^ e else 0) =
      (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) := by
    by_cases h : n = M * m + j * e
    · rw [if_pos h, if_pos h, val_mul_pow_pow, zeta_pow_of_eq ζ hζ h]; ring
    · rw [if_neg h, if_neg h, mul_zero]
  have S2 : (ζ : K) ^ n * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) =
      (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) := by
    by_cases h : n + j * e = M * m
    · rw [if_pos h, if_pos h, ← val_inv_mul_pow_pow c ζ j e]
      have hz : (ζ : K) ^ n * (ζ : K) ^ (j * e) = 1 := zeta_pow_mul_of_add_eq ζ hζ h
      linear_combination ((((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e) * hz
    · rw [if_neg h, if_neg h, mul_zero]
  have S3 : (ζ : K) ^ n * (if n = M * m then (1 : K) else 0) = (if n = M * m then 1 else 0) := by
    by_cases h : n = M * m
    · rw [if_pos h]
      have := zeta_pow_of_eq ζ hζ (t := 0) (m := m) (n := n) (by omega)
      rw [this, pow_zero, mul_one]
    · rw [if_neg h, mul_zero]
  calc (ζ : K) ^ n * (α * (if n = M * m + j * e then (c : K) ^ e else 0) +
        β * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        γ * (if n = M * m then 1 else 0))
        = α * ((ζ : K) ^ n * (if n = M * m + j * e then (c : K) ^ e else 0)) +
          β * ((ζ : K) ^ n * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0)) +
          γ * ((ζ : K) ^ n * (if n = M * m then 1 else 0)) := by ring
    _ = _ := by rw [S1, S2, S3]

theorem head_twist (ζ : Kˣ) (c : Kˣ) (j n : ℕ) (hj : 0 < j) (δ : ℕ → K) :
    (ζ : K) ^ n * (if j ∣ n then δ (n / j) * (c : K) ^ (n / j) else 0) =
      (if j ∣ n then δ (n / j) * ((c * ζ ^ j : Kˣ) : K) ^ (n / j) else 0) := by
  split_ifs with hjn
  · obtain ⟨d, rfl⟩ := hjn
    rw [Nat.mul_div_cancel_left d hj, val_mul_pow_pow]
    ring
  · rw [mul_zero]

theorem rescale_slotSubst_tateUnivX (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    PowerSeries.rescale (ζ : K) (slotSubst K M c j tateUnivX) =
      slotSubst K M (c * ζ ^ j) j tateUnivX := by
  ext n
  rw [PowerSeries.coeff_rescale, coeff_slotSubst_tateUnivX M c j hj hjM n,
    coeff_slotSubst_tateUnivX M (c * ζ ^ j) j hj hjM n, mul_add, Finset.mul_sum]
  congr 1
  · exact head_twist ζ c j n hj (fun d => ((d : ℕ) : K))
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := term_twist ζ hζ c j n m e hj (e : K) (e : K) (-(2 * (e : K)))
    have lhs : (e : K) * ((if n = M * m + j * e then (c : K) ^ e else 0) +
        (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) - (if n = M * m then 2 else 0)) =
        (e : K) * (if n = M * m + j * e then (c : K) ^ e else 0) +
        (e : K) * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        (-(2 * (e : K))) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    have rhs : (e : K) * ((if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) +
        (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) -
        (if n = M * m then 2 else 0)) =
        (e : K) * (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) +
        (e : K) * (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        (-(2 * (e : K))) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    rw [lhs, rhs, this]

theorem rescale_slotSubst_tateUnivY (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    PowerSeries.rescale (ζ : K) (slotSubst K M c j tateUnivY) =
      slotSubst K M (c * ζ ^ j) j tateUnivY := by
  ext n
  rw [PowerSeries.coeff_rescale, coeff_slotSubst_tateUnivY M c j hj hjM n,
    coeff_slotSubst_tateUnivY M (c * ζ ^ j) j hj hjM n, mul_add, Finset.mul_sum]
  congr 1
  · exact head_twist ζ c j n hj (fun d => (((d.choose 2 : ℕ)) : K))
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := term_twist ζ hζ c j n m e hj (((e.choose 2 : ℕ)) : K)
      (-((((e + 1).choose 2 : ℕ)) : K)) (e : K)
    have lhs : ((if n = M * m + j * e then (((e.choose 2 : ℕ)) : K) * (c : K) ^ e else 0) -
        (if n + j * e = M * m then ((((e + 1).choose 2 : ℕ)) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        (if n = M * m then (e : K) else 0)) =
        (((e.choose 2 : ℕ)) : K) * (if n = M * m + j * e then (c : K) ^ e else 0) +
        (-((((e + 1).choose 2 : ℕ)) : K)) *
          (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        (e : K) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    have rhs : ((if n = M * m + j * e then (((e.choose 2 : ℕ)) : K) * ((c * ζ ^ j : Kˣ) : K) ^ e
          else 0) -
        (if n + j * e = M * m then
          ((((e + 1).choose 2 : ℕ)) : K) * (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        (if n = M * m then (e : K) else 0)) =
        (((e.choose 2 : ℕ)) : K) * (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) +
        (-((((e + 1).choose 2 : ℕ)) : K)) *
          (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        (e : K) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    rw [lhs, rhs, this]

theorem main (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    (qTwist ζ (nonToricPoint K M c j).1, qTwist ζ (nonToricPoint K M c j).2) =
      nonToricPoint K M (c * ζ ^ j) j := by
  rw [nonToricPoint, nonToricPoint, Prod.mk.injEq, qTwist_ofPowerSeries, qTwist_ofPowerSeries,
    rescale_slotSubst_tateUnivX M ζ hζ c j hj hjM, rescale_slotSubst_tateUnivY M ζ hζ c j hj hjM]
  exact ⟨rfl, rfl⟩

end P2MKcQTwistSlot

open ModularCurve

universe u in
theorem solution
    (K : Type u) [CommRing K] (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    (qTwist ζ (nonToricPoint K M c j).1, qTwist ζ (nonToricPoint K M c j).2) =
      nonToricPoint K M (c * ζ ^ j) j :=
  P2MKcQTwistSlot.main M ζ hζ c j hj hjM

end S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one
end P2MW
export P2MW.S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one (solution)
