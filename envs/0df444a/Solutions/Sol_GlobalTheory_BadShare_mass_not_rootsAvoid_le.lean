-- Prove2me | solution 1 for GlobalTheory.BadShare.mass_not_rootsAvoid_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:22:18.145562+00:00
-- url     : https://prove2.me/submissions/2e35c896-7bcf-49b1-a248-2f93423a4a6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumLeProdOfTwoLeNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLe
import Theorems.Thm_GlobalTheory_BadShare_avoid_sum_le
import Theorems.Thm_GlobalTheory_BadShare_avoid_mass_le_sum
import Theorems.Thm_GlobalTheory_BadShare_sum_primePowerPart_pow_sub_one_le
import Theorems.Thm_GlobalTheory_BadShare_sum_primePowerParts_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  rintro g _ N q d c ⟨hq, hd, hq2, hd2, hqd, hmax, hdvd⟩
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have h4 : 4 ∣ g - 1 := Dvd.dvd.trans ⟨4 * q * d, by ring⟩ hdvd
  refine (avoid_mass_le_sum c N (Dvd.dvd.trans (by norm_num) h4)).trans ?_
  cases N with
  | zero => simp only [Nat.cast_zero, Real.log_zero]; simp; positivity
  | succ N =>
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega), Finset.sum_insert (by simp)]
    refine add_le_add ?_ ?_
    · have h := GlobalTheory.BadShare.sum_primePowerParts_le (g - 1) q d (by omega) hq hd hq2 hd2 hqd hmax hdvd
      rw [Nat.cast_sub (by omega)] at h
      simp only [pow_one, Nat.cast_one, one_mul] at h ⊢
      rw [div_le_iff₀ hg1]
      refine h.trans_eq ?_
      ring
    · refine le_trans (Finset.sum_le_sum fun e he => ?_) ((avoid_sum_le g hgR N).trans ?_)
      · have he2 : 2 ≤ e := (Finset.mem_Icc.1 he).1
        have he0 : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
        have hq : (0 : ℝ) < (g : ℝ) ^ e - 1 := by
          have : (1 : ℝ) < (g : ℝ) ^ e := one_lt_pow₀ (by linarith) (by omega)
          linarith
        rw [div_le_iff₀ (by positivity)]
        refine (GlobalTheory.BadShare.sum_primePowerPart_pow_sub_one_le g e hg h4 he2).trans_eq ?_
        field_simp
      · refine div_le_div_of_nonneg_right ?_ hg1.le
        have : (0 : ℝ) ≤ 1 / (g : ℝ) ^ N := by positivity
        linarith
end GlobalTheory.BadShare
