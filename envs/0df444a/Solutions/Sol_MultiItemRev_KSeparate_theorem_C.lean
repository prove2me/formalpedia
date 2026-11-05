-- Prove2me | solution 1 for MultiItemRev.KSeparate.theorem_C
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:19:15.49792+00:00
-- url     : https://prove2.me/submissions/d475fd11-91fc-45dd-9b51-f87ee82f6c6a

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model
import Theorems.Thm_MultiItemRev_KSeparate_proposition_13_ii
import Theorems.Thm_MultiItemRev_KSeparate_power_of_two_bound
import Theorems.Thm_MultiItemRev_KSeparate_zero_padding

open MeasureTheory
open scoped NNReal ENNReal

namespace KSepThmCAux
open MultiItemRev.Decomp

/-- A good with value identically zero yields no revenue. -/
lemma rev1_dirac_zero : Rev1 (Measure.dirac 0) = 0 := by
  unfold Rev1 Rev
  refine le_antisymm (iSup₂_le fun M hM => ?_) zero_le
  obtain ⟨_, _, hIR, hm⟩ := hM
  have hmap : oneGood (Measure.dirac (0 : ℝ≥0)) = Measure.dirac (fun _ : Unit => (0 : ℝ≥0)) := by
    rw [oneGood, Measure.map_dirac' (by fun_prop)]
  have hs : M.s (fun _ => 0) ≤ 0 := by
    have := hIR (fun _ => 0)
    unfold buyerPayoff at this
    simp at this
    linarith
  rw [hmap]
  apply le_of_eq
  apply EReal.toENNReal_of_nonpos
  unfold expRevenue
  rw [lintegral_dirac' _ (f := fun x => ENNReal.ofReal (M.s x))
      (ENNReal.measurable_ofReal.comp hm),
    lintegral_dirac' _ (f := fun x => ENNReal.ofReal (-M.s x))
      (ENNReal.measurable_ofReal.comp hm.neg),
    ENNReal.ofReal_of_nonpos hs]
  simp

lemma map_eval_pi {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    (Measure.pi ν).map (fun x => x i) = ν i := by
  classical
  have := Measure.pi_map_eval (μ := ν) i
  simp only [measure_univ, Finset.prod_const_one, one_smul] at this
  exact this

lemma srev_pi {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] :
    SRev (Measure.pi ν) = ∑ i, Rev1 (ν i) := by
  unfold SRev
  simp only [map_eval_pi]

lemma logb_two_pow (m : ℕ) : Real.logb 2 ((2 ^ m : ℕ) : ℝ) = (m : ℝ) := by
  push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

end KSepThmCAux

open KSepThmCAux MultiItemRev.Decomp in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)],
        ENNReal.ofReal (c / Real.log (k : ℝ) ^ 2) *
          MultiItemRev.Decomp.Rev (Measure.pi ν) ≤ MultiItemRev.Decomp.SRev (Measure.pi ν) := by
  obtain ⟨c, hcpos, hc⟩ := MultiItemRev.KSeparate.proposition_13_ii
  set c' : ℝ := min c (1 / 2 : ℝ) with hc'
  have hc'pos : 0 < c' := lt_min hcpos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c' * Real.log 2 ^ 2 / 4, by positivity, fun k hk ν _ => ?_⟩
  -- choose the power of two
  set m := Nat.clog 2 k with hmdef
  have hm1 : 1 ≤ m := Nat.clog_pos (by norm_num) (by omega)
  have hkm : k ≤ 2 ^ m := Nat.le_pow_clog (by norm_num) k
  have hlt : 2 ^ (m - 1) < k := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < k by omega)
    simpa [Nat.pred_eq_sub_one] using this
  set j := 2 ^ m - k with hj
  have hN : k + j = 2 ^ m := by omega
  -- the power-of-two bound, transported to `k + j` goods
  have P := MultiItemRev.KSeparate.power_of_two_bound c hcpos hc m hm1
  rw [logb_two_pow, ← hN] at P
  have hinst : ∀ i, IsProbabilityMeasure
      (Fin.append ν (fun _ : Fin j => Measure.dirac (0 : ℝ≥0)) i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun l => ?_) i
    · rw [Fin.append_left]; infer_instance
    · rw [Fin.append_right]; infer_instance
  have hP := P (Fin.append ν (fun _ : Fin j => Measure.dirac 0))
  rw [MultiItemRev.KSeparate.zero_padding k j ν, Fin.sum_univ_add] at hP
  simp only [Fin.append_left, Fin.append_right, rev1_dirac_zero, Finset.sum_const_zero,
    add_zero] at hP
  rw [srev_pi]
  -- the real inequality `m ≤ 2 log₂ k`
  set L := Real.log (k : ℝ) with hL
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hk2
  have hmL : (m : ℝ) * Real.log 2 ≤ 2 * L := by
    have h1 : ((2 ^ (m - 1) : ℕ) : ℝ) < k := by exact_mod_cast hlt
    have h2 : ((m - 1 : ℕ) : ℝ) * Real.log 2 < L := by
      rw [hL, ← Real.log_rpow (by norm_num)]
      apply Real.log_lt_log (by positivity)
      rw [Real.rpow_natCast]
      exact_mod_cast h1
    have h3 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm1]; simp
    rw [h3] at h2
    nlinarith
  have hcoef : c' * Real.log 2 ^ 2 / 4 / L ^ 2 * (1 / c' * (m : ℝ) ^ 2) ≤ 1 := by
    rw [div_div, div_mul_eq_mul_div, div_le_one (by positivity)]
    have hm0 : (0 : ℝ) ≤ m * Real.log 2 := by positivity
    have : ((m : ℝ) * Real.log 2) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hm0 hmL 2
    field_simp
    nlinarith
  calc ENNReal.ofReal (c' * Real.log 2 ^ 2 / 4 / L ^ 2) * Rev (Measure.pi ν)
      ≤ ENNReal.ofReal (c' * Real.log 2 ^ 2 / 4 / L ^ 2) *
          (ENNReal.ofReal (1 / c' * (m : ℝ) ^ 2) * ∑ i, Rev1 (ν i)) := by gcongr
    _ = ENNReal.ofReal (c' * Real.log 2 ^ 2 / 4 / L ^ 2 * (1 / c' * (m : ℝ) ^ 2)) *
          ∑ i, Rev1 (ν i) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ 1 * ∑ i, Rev1 (ν i) := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hcoef
    _ = ∑ i, Rev1 (ν i) := one_mul _
