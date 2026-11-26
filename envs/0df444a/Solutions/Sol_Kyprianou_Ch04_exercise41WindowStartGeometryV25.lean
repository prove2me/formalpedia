-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41WindowStartGeometryV25
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:35:27.686798+00:00
-- url     : https://prove2.me/submissions/d2de5e5e-4aa0-43cc-8480-f19ffc76152a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (s e h : NNReal) (hs : 0 < s) (hh : 0 < h) (hhe : h < e) (hhs : h < s)
    (r : ℝ) (hr : r ∈ Ioo ((s : ℝ)-(h : ℝ)) (s : ℝ)) :
    0 ≤ r ∧ r.toNNReal ≤ s ∧ s < r.toNNReal+h ∧
      Icc r.toNNReal (r.toNNReal+h) ⊆ Icc (s-e) (s+e) := by
  have hh' : (h : ℝ) < (s : ℝ) := by exact_mod_cast hhs
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hrr : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ hr0
  have h1 : r.toNNReal ≤ s := by
    exact_mod_cast (show (r.toNNReal : ℝ) ≤ (s : ℝ) by rw [hrr]; exact hr.2.le)
  have h2 : s < r.toNNReal+h := by
    exact_mod_cast (show (s : ℝ) < ((r.toNNReal+h : NNReal) : ℝ) by
      rw [NNReal.coe_add,hrr]; linarith [hr.1])
  have h3 : s-h ≤ r.toNNReal := by
    exact_mod_cast (show ((s-h : NNReal) : ℝ) ≤ (r.toNNReal : ℝ) by
      rw [NNReal.coe_sub hhs.le,hrr]; exact hr.1.le)
  refine ⟨hr0,h1,h2,?_⟩
  intro u hu
  exact ⟨(tsub_le_tsub_left hhe.le s).trans (h3.trans hu.1),
    hu.2.trans (add_le_add h1 hhe.le)⟩
