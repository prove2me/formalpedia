-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RealGermFromNNRealV16
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:13:28.082288+00:00
-- url     : https://prove2.me/submissions/53d79743-bf77-4a27-9a26-296a357bca1f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (e : NNReal) (he : 0 < e)
    (h : ∀ u : NNReal, 0 < u → u < e → x (s.toNNReal + u) - x s.toNNReal > 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Ioo s (s+δ), x s.toNNReal < x v.toNNReal := by
  refine ⟨(e : ℝ),by exact_mod_cast he,?_⟩
  intro v hv
  let u := Real.toNNReal (v-s)
  have huv : (u : ℝ) = v-s := Real.coe_toNNReal _ (sub_nonneg.mpr hv.1.le)
  have hu : 0 < u := by exact_mod_cast (show (0 : ℝ) < (u : ℝ) by rw [huv]; linarith [hv.1])
  have hlt : u < e := by exact_mod_cast (show (u : ℝ) < (e : ℝ) by rw [huv]; linarith [hv.2])
  have heq : s.toNNReal + u = v.toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ hs,huv,Real.coe_toNNReal _ (hs.trans hv.1.le)]
    ring
  have H := h u hu hlt
  rw [heq] at H
  linarith
