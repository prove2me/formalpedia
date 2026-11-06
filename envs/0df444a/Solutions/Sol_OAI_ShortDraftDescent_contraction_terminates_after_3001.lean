-- Prove2me | solution 1 for OAI.ShortDraftDescent.contraction_terminates_after_3001
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:22.26883+00:00
-- url     : https://prove2.me/submissions/617f6869-b12b-4e07-8c65-43edbc2bd3ab

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftDescent
namespace OAI.ShortDraftDescent
theorem _root_.solution
    (z : ℝ) (K : ℕ → ℝ) (hz : 1 < z)
    (hK0 : K 0 ≤ z ^ 3000)
    (hcontract : ∀ n, K (n + 1) ≤ K n / z) :
    K 3001 < 1 := by
  have hz0 : 0 < z := by linarith
  have hbound (n : ℕ) : K n * z ^ n ≤ K 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hcontract n
        have hstep : K (n + 1) * z ≤ K n := by
          exact (le_div_iff₀ hz0).mp hs
        calc
          K (n + 1) * z ^ (n + 1) =
              (K (n + 1) * z) * z ^ n := by rw [pow_succ]; ring
          _ ≤ K n * z ^ n :=
            mul_le_mul_of_nonneg_right hstep (pow_nonneg (le_of_lt hz0) n)
          _ ≤ K 0 := ih
  have h3001 := hbound 3001
  have hpow : z ^ 3000 < z ^ 3001 := by
    calc
      z ^ 3000 = z ^ 3000 * 1 := by ring
      _ < z ^ 3000 * z :=
        mul_lt_mul_of_pos_left hz (pow_pos hz0 _)
      _ = z ^ 3001 := by ring
  have hlt : K 3001 * z ^ 3001 < z ^ 3001 :=
    lt_of_le_of_lt (h3001.trans hK0) hpow
  by_contra h
  have hge : 1 ≤ K 3001 := le_of_not_gt h
  nlinarith [mul_nonneg (sub_nonneg.mpr hge)
    (le_of_lt (pow_pos hz0 3001))]
end OAI.ShortDraftDescent
