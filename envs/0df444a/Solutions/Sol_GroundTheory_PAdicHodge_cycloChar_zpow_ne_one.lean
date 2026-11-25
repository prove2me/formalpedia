-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cycloChar_zpow_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:42:03.821006+00:00
-- url     : https://prove2.me/submissions/46831732-cd23-4c24-908f-aef2bfcaac51

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
import Theorems.Thm_GroundTheory_PAdicHodge_one_add_pow_ne_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_cycloChar_sub_one_le
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
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
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : cycloChar K σ ^ j ≠ 1 := by
  intro hpow
  have hm : cycloChar K σ ^ j.natAbs = 1 := by
    rcases Int.natAbs_eq j with hj' | hj'
    · rw [hj', zpow_natCast] at hpow; exact hpow
    · rw [hj', zpow_neg, inv_eq_one, zpow_natCast] at hpow; exact hpow
  set u : ℤ_[p] := ((cycloChar K σ : ℤ_[p]ˣ) : ℤ_[p])
  set w : PadicAlgCl p := algebraMap ℚ_[p] (PadicAlgCl p) ((u - 1 : ℤ_[p]) : ℚ_[p])
  have hw0 : w ≠ 0 := by
    intro hw
    rw [map_eq_zero, PadicInt.coe_eq_zero, sub_eq_zero] at hw
    exact hne (Units.ext hw)
  have hw : ‖w‖ < (p : ℝ)⁻¹ := by
    rw [norm_algebraMap', ← PadicInt.norm_def]
    refine (norm_cycloChar_sub_one_le K σ 2 h2).trans_lt ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hp1 (by norm_num)
  apply one_add_pow_ne_one hw0 hw (Int.natAbs_ne_zero.2 hj)
  have h1 : (1 : PadicAlgCl p) + w = algebraMap ℚ_[p] (PadicAlgCl p) (u : ℚ_[p]) := by
    simp [w, u]
  rw [h1, ← map_pow, ← PadicInt.coe_pow, ← Units.val_pow_eq_pow_val, hm]
  simp
end GroundTheory.PAdicHodge
