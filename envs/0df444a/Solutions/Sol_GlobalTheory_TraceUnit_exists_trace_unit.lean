-- Prove2me | solution 1 for GlobalTheory.TraceUnit.exists_trace_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:13.605481+00:00
-- url     : https://prove2.me/submissions/d3bcd224-9786-4da0-8ae2-ee066f033ce2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
import Theorems.Thm_GlobalTheory_TraceUnit_norm_sub_le_max_of_ultra
import Theorems.Thm_GlobalTheory_TraceUnit_norm_pow_two_pow_sub_le
import Theorems.Thm_GlobalTheory_TraceUnit_norm_sub_lt_one_of_pow
import Theorems.Thm_GlobalTheory_TraceUnit_exists_pow_close

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TraceUnit
namespace GlobalTheory.TraceUnit
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E],
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
      ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by
  intro F E _ _ _ _ hU htr
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : CharZero F := hU.charZero
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  have h20 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have h2le : ‖(2 : E)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one E 2
    simpa using this
  rcases h2le.lt_or_eq with h2 | h2
  swap
  ·
    refine ⟨2⁻¹, by rw [norm_inv, h2, inv_one], ?_⟩
    have hs : star (2⁻¹ : E) = 2⁻¹ := by
      have : (2⁻¹ : E) = algebraMap F E 2⁻¹ := by rw [map_inv₀, map_ofNat]
      rw [this, hU.star_fix]
    rw [← norm_algebraMap' E, htr, hs, ← two_mul, mul_inv_cancel₀ h20, norm_one]

  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ a : F, y - algebraMap F E a ≠ 0 := fun a h => hy (by rw [sub_eq_zero.1 h, hU.star_fix])
  have hcont : Continuous fun a : F => ‖y - algebraMap F E a‖ := by fun_prop
  obtain ⟨x, -, hx⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    (Metric.nonempty_closedBall.2 (norm_nonneg _)) hcont.continuousOn
  have hmin : ∀ a : F, ‖y - algebraMap F E x‖ ≤ ‖y - algebraMap F E a‖ := by
    intro a
    have h0 : ‖y - algebraMap F E x‖ ≤ ‖y‖ := by
      have := isMinOn_iff.1 hx 0 (Metric.mem_closedBall_self (norm_nonneg y))
      simpa using this
    by_cases ha : ‖a‖ ≤ ‖y‖
    · exact isMinOn_iff.1 hx a (mem_closedBall_zero_iff.2 ha)
    · push_neg at ha
      have hm : ‖a‖ ≤ max ‖y‖ ‖y - algebraMap F E a‖ := by
        have := norm_sub_le_max_of_ultra y (y - algebraMap F E a)
        rwa [sub_sub_cancel, norm_algebraMap'] at this
      rcases le_max_iff.1 hm with h | h <;> linarith
  obtain ⟨t, ht⟩ := hU.unram (y - algebraMap F E x)
  have hd : 0 < ‖y - algebraMap F E x‖ := norm_pos_iff.2 (hyF x)
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [← norm_algebraMap' E t, h0, norm_zero] at ht
    linarith
  set u := (y - algebraMap F E x) * (algebraMap F E t)⁻¹ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_inv, norm_algebraMap', ← ht, mul_inv_cancel₀ hd.ne']
  have hfar : ∀ a : F, 1 ≤ ‖u - algebraMap F E a‖ := by
    intro a
    have e : u - algebraMap F E a = (y - algebraMap F E (x + t * a)) * (algebraMap F E t)⁻¹ := by
      rw [hu, map_add, map_mul]
      field_simp
      ring
    rw [e, norm_mul, norm_inv, norm_algebraMap', ← ht, le_mul_inv_iff₀ hd, one_mul]
    exact hmin _
  refine ⟨u, hu1.le, ?_⟩
  have hle : ‖Algebra.trace F E u‖ ≤ 1 := by
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu1.le (by rw [hU.norm_star]; exact hu1.le))
  refine le_antisymm hle (not_lt.1 fun hs => ?_)

  set n := u * star u with hn
  have hnn : star n = n := by rw [hn, star_mul, star_star, mul_comm]
  set v : F := -(Algebra.trace F E n / 2) with hvd
  have hv : algebraMap F E v = -n := by
    rw [hvd, map_neg, map_div₀, htr, hnn, map_ofNat]
    field_simp
    ring
  have hvn : ‖algebraMap F E v‖ ≤ 1 := by
    rw [hv, norm_neg, hn, norm_mul, hU.norm_star, hu1, one_mul]
  have hq : ‖u ^ 2 - algebraMap F E v‖ < 1 := by
    have e : u ^ 2 - algebraMap F E v = algebraMap F E (Algebra.trace F E u) * u := by
      rw [hv, htr, hn]; ring
    rw [e, norm_mul, norm_algebraMap', hu1, mul_one]
    exact hs
  obtain ⟨i, j, hij, hc⟩ := exists_pow_close hu1.le
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  have e1 : u ^ 2 ^ (i + (m + 1)) = (u ^ 2 ^ (m + 1)) ^ 2 ^ i := by
    rw [← pow_mul, ← pow_add, Nat.add_comm (m + 1) i]
  rw [e1] at hc
  have hpow1 : ‖u ^ 2 ^ (m + 1)‖ ≤ 1 := by rw [norm_pow, hu1, one_pow]
  have hA : ‖u - u ^ 2 ^ (m + 1)‖ < 1 := norm_sub_lt_one_of_pow h2 hu1.le hpow1 i hc
  have e2 : u ^ 2 ^ (m + 1) = (u ^ 2) ^ 2 ^ m := by rw [pow_succ', pow_mul]
  have hB : ‖(u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m‖ < 1 :=
    (norm_pow_two_pow_sub_le (by rw [norm_pow, hu1, one_pow]) hvn m).trans_lt hq
  have hC : ‖u - algebraMap F E (v ^ 2 ^ m)‖ < 1 := by
    rw [map_pow]
    have e3 : u - (algebraMap F E v) ^ 2 ^ m =
        (u - u ^ 2 ^ (m + 1)) + ((u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m) := by
      rw [e2]; ring
    rw [e3]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hA hB)
  linarith [hfar (v ^ 2 ^ m)]
end GlobalTheory.TraceUnit
