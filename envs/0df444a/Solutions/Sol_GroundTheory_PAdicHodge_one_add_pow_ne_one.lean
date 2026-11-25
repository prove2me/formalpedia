-- Prove2me | solution 1 for GroundTheory.PAdicHodge.one_add_pow_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:53.289902+00:00
-- url     : https://prove2.me/submissions/676c1e7f-7658-40d8-a31a-87492a7f4086

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_padicAlgCl
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {w : PadicAlgCl p} (hw0 : w ≠ 0) (hw : ‖w‖ < (p : ℝ)⁻¹) {m : ℕ}
    (hm : m ≠ 0) : (1 + w) ^ m ≠ 1 := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hexp : (1 + w) ^ (m' + 1) - 1 = ((m' + 1 : ℕ) : PadicAlgCl p) * w +
      ∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) := by
    rw [add_comm (1 : PadicAlgCl p) w, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_one,
      Nat.choose_one_right, zero_add]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hmpos : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
    rw [norm_pos_iff]; exact_mod_cast Nat.succ_ne_zero m'
  have hlead : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rw [norm_mul]; exact mul_pos hmpos hwpos

  have hterm : ∀ k ∈ Finset.range m', ‖w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    intro k _

    have hch : ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) * ((k + 1 + 1 : ℕ) : PadicAlgCl p) =
        ((m' + 1 : ℕ) : PadicAlgCl p) * (m'.choose (k + 1) : PadicAlgCl p) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m' (k + 1)).symm
    have hk0 : (k + 1 + 1 : ℕ) ≠ 0 := by omega
    have hknorm : ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by
      rw [norm_natCast_padicAlgCl hk0, zpow_neg, zpow_natCast]
      gcongr
      exact_mod_cast Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hkpos : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hC : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ ≤
        ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ) := by
      have h1 := congrArg norm hch
      rw [norm_mul, norm_mul] at h1
      have h2 : ‖(m'.choose (k + 1) : PadicAlgCl p)‖ ≤ 1 :=
        IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) _
      have h3 : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤
          ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
        calc _ ≤ ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ *
              ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by gcongr
          _ = _ := h1
          _ ≤ ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * 1 := by gcongr
          _ = _ := mul_one _
      rwa [← div_eq_mul_inv, div_le_iff₀ hkpos] at h3

    have hpow : ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < 1 := by
      have h1 : ‖w‖ ^ (k + 1) < ((p : ℝ)⁻¹) ^ (k + 1) :=
        pow_lt_pow_left₀ hw (norm_nonneg _) (Nat.succ_ne_zero k)
      have h2 : ((k + 1 + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
        have := Nat.lt_pow_self (n := k + 1) hp.out.one_lt
        exact_mod_cast this
      calc ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < ((k + 1 + 1 : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ (k + 1) :=
            mul_lt_mul_of_pos_left h1 hkpos
        _ ≤ (p : ℝ) ^ (k + 1) * ((p : ℝ)⁻¹) ^ (k + 1) := by gcongr
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    rw [norm_mul, norm_pow, norm_mul]
    calc ‖w‖ ^ (k + 1 + 1) * ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
        ≤ ‖w‖ ^ (k + 1 + 1) * (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)) := by
          gcongr
      _ = (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * (((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1)) := by
          ring
      _ < (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * 1 :=
          mul_lt_mul_of_pos_left hpow (mul_pos hmpos hwpos)
      _ = _ := mul_one _
  have htail : ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rcases (Finset.range m').eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty, norm_zero]; exact hlead
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun k => w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p))
      exact hle.trans_lt (hterm i hi)
  intro h
  have h0 : (1 + w) ^ (m' + 1) - 1 = 0 := by rw [h, sub_self]
  rw [hexp] at h0
  have hne : ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ ≠
      ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ :=
    htail.ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [h0, norm_zero] at this
  exact hlead.ne (this.trans (max_eq_left htail.le))
end GroundTheory.PAdicHodge
