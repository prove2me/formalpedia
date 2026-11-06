-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:04:51.243982+00:00
-- url     : https://prove2.me/submissions/1a538756-54e8-4281-bd5c-63976f4180bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_2
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_bound_on_6
import Theorems.Thm_LostSalesExpGap_ConstOrder_g_pos_opt_ge_g
import Theorems.Thm_LostSalesExpGap_ConstOrder_vartheta_pos_gamma_lt_one

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open LostSalesExpGap.ConstOrder in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    constCost P c (rInf P c) / CappedBaseStock.OPT P c ≤
      ENNReal.ofReal (1 + c.h * ((1 - gamma P c) * gNV P c)⁻¹ *
        ((CappedBaseStock.mean P - rInf P c) + varthetaInv P c / (Real.exp 1 * ((c.L : ℝ) + 1))) *
        gamma P c ^ (c.L + 1)) := by
  obtain ⟨_, hCfin, hOfin, hIfin, h5⟩ := lemma_2 P c hP
  obtain ⟨_, _, h3⟩ := lemma_3 P c hP
  have h6 := bound_on_6 P c hP c.L c.leadTime_pos
  obtain ⟨hg, hOg⟩ := g_pos_opt_ge_g P c hP
  obtain ⟨hγ0, hγ1, hϑ⟩ := vartheta_pos_gamma_lt_one P c hP
  have hh := c.holding_pos
  set γ := gamma P c
  set g := gNV P c
  set ϑi := varthetaInv P c
  set C := constCost P c (rInf P c)
  set O := CappedBaseStock.OPT P c
  set m := CappedBaseStock.mean P
  set r := rInf P c
  set L := c.L
  -- nonnegativity facts
  have hϑi : 0 ≤ ϑi := by
    simp only [ϑi, varthetaInv]
    split_ifs with hs
    · apply inv_nonneg.mpr
      obtain ⟨θ, hθ⟩ := hs.1
      exact le_trans hθ.1 (le_csSup hs.2 hθ)
    · exact le_refl _
  have hmean : 0 < m := P.positiveMean
  have hrm : r ≤ m := by
    simp only [r, rInf]
    by_cases hne : (argminConst P c).Nonempty
    · obtain ⟨x, hx⟩ := hne
      exact le_trans (csInf_le ⟨0, fun y hy => hy.1.1⟩ hx) hx.1.2
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]; exact hmean.le
  have hEIL : 0 ≤ EIL P r L := by
    apply integral_nonneg
    intro d
    simp only [CappedBaseStock.finiteInventory]
    exact le_trans (by simp) (Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
      (Finset.mem_range.mpr (Nat.succ_pos L)))
  have h1γ : 0 < 1 - γ := by linarith
  have hγL : 0 ≤ γ ^ (L + 1) := pow_nonneg hγ0 _
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  set X := ((1 - γ) * Real.exp 1 * ((L : ℝ) + 1))⁻¹ * ϑi * γ ^ (L + 1) with hX
  have hX0 : 0 ≤ X := by positivity
  have h3L := h3 L c.leadTime_pos
  have hI : (EIinf P r).toReal ≤ EIL P r L + X := by
    have := ENNReal.toReal_mono (by simp) h3L
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hEIL, ENNReal.toReal_ofReal hX0] at this
  set B := c.h * X + c.h * (m - r) * (1 - γ)⁻¹ * γ ^ (L + 1) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ m - r := by linarith
    positivity
  have hdiff : C.toReal - O.toReal ≤ B := by
    have := mul_le_mul_of_nonneg_left hI hh.le
    simp only [hB]; nlinarith [h5, h6, this]
  -- OPT bounds
  have hOg' : g ≤ O.toReal := by
    have := ENNReal.toReal_mono hOfin hOg
    rwa [ENNReal.toReal_ofReal hg.le] at this
  have hOpos : 0 < O.toReal := lt_of_lt_of_le hg hOg'
  have hO0 : O ≠ 0 := by
    intro h0; rw [h0] at hOpos; simp at hOpos
  have hratio : C.toReal / O.toReal ≤ 1 + B / g := by
    rw [div_le_iff₀ hOpos]
    have : B ≤ B / g * O.toReal := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hg]
      exact mul_le_mul_of_nonneg_left hOg' hB0
    nlinarith
  have hrhs : 1 + B / g = 1 + c.h * ((1 - γ) * g)⁻¹ *
        ((m - r) + ϑi / (Real.exp 1 * ((L : ℝ) + 1))) * γ ^ (L + 1) := by
    simp only [hB, hX]
    field_simp
    ring
  have hCdiv : C / O = ENNReal.ofReal (C.toReal / O.toReal) := by
    rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal]
    exact ENNReal.div_ne_top hCfin hO0
  rw [hCdiv, ← hrhs]
  exact ENNReal.ofReal_le_ofReal hratio
