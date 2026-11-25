-- Prove2me | solution 1 for Newton.continuous_compactSupport_dense_Lp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:34:47.628803+00:00
-- url     : https://prove2.me/submissions/244a3ea0-ae7e-4fdb-bf1f-66550a7e8018

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (p : ℝ≥0∞)
    (hp_ne_top : p ≠ ⊤)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      MemLp g p volume ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε := by
  -- apply the standard Lᵖ-density result for compactly supported continuous functions
  have hε_half_pos : 0 < ε / 2 := by
    have : (0 : ℝ) < 2 := by norm_num
    exact div_pos hε this
  have hε_half_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    have : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr hε_half_pos
    exact ne_of_gt this
  obtain ⟨g, hg_compact, hg_bound, hg_cont, hg_memLp⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hp_ne_top hε_half_ne
  have h_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
    have h_half_lt : ε / 2 < ε := by simpa using half_lt_self hε
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 h_half_lt
  refine ⟨g, hg_cont, hg_compact, hg_memLp, ?_⟩
  exact lt_of_le_of_lt hg_bound h_lt
end Newton
