-- Prove2me | solution 1 for OAI.RuledApproximation.hyperbolic_lattice_model
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:44:10.395212+00:00
-- url     : https://prove2.me/submissions/36346a2e-6dfb-4947-bace-41d794fa2e17

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/HyperbolicLattice.lean:L28-L82
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.hyperbolic_lattice_model. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Theorems.Thm_OAI_RuledApproximation_lattice_covering

-- ---- from OAI.Geometry.RuledCovering.HyperbolicLattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma norm_le_of_scaled_coordinates {n C : ℝ} (hn : 0 < n) (hC : 0 ≤ C)
    (x : Parameter) (hx : ∀ i, |n * x i| ≤ C) : ‖x‖ ≤ C / n := by
  rw [pi_norm_le_iff_of_nonneg (div_nonneg hC hn.le)]
  intro i
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ hn).2
  have := hx i
  rwa [abs_mul, abs_of_pos hn, mul_comm] at this

/-- The symmetric hyperbolic template, with its uniform distance bound. -/
theorem hyperbolic_lattice_model {L lam : ℝ} (hL : 0 < L)
    (hlam : 0 < L * lam) (hsmall : L * lam < 1) :
    LatticeModel (lam • swapCLM) L (1 / (2 * (1 - L * lam))) := by
  have hlampos : 0 < lam := by nlinarith
  intro n hn p r hr
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have har : |r * lam| ≤ L * lam := by
    rw [abs_mul, abs_of_pos hlampos]
    exact mul_le_mul_of_nonneg_right hr hlampos.le
  have ha : |r * lam| < 1 := har.trans_lt hsmall
  obtain ⟨i, j, hi, hj, hd⟩ := lattice_covering (r * lam) ha
    ((n : ℝ) * p 0) ((n : ℝ) * p 1)
  let b : Parameter := ![(i : ℝ) / n, (j : ℝ) / n]
  have : NeZero n := ⟨hn.ne'⟩
  have hbgrid : b ∈ coordinateGrid n := by
    apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
    intro k
    fin_cases k
    · refine ⟨i, ?_⟩
      simp [b, mul_div_cancel₀, hnreal.ne']
    · refine ⟨j, ?_⟩
      simp [b, mul_div_cancel₀, hnreal.ne']
  have hd' : max |(n : ℝ) * p 0 - i| |(n : ℝ) * p 1 - j| ≤
      1 / (2 * (1 - L * lam)) := hd.trans
        (one_div_le_one_div_of_le (by positivity) (by linarith))
  refine ⟨b, hbgrid, ?_, ?_⟩
  · rw [dist_eq_norm, norm_sub_rev]
    apply norm_le_of_scaled_coordinates hnreal (by positivity)
    intro k
    fin_cases k
    · have heq : (n : ℝ) * (p - b) 0 = (n : ℝ) * p 0 - i := by
        simp [b, mul_sub, mul_div_cancel₀, hnreal.ne']
      change |(n : ℝ) * (p - b) 0| ≤ _
      rw [heq]
      exact (le_max_left _ _).trans hd'
    · have heq : (n : ℝ) * (p - b) 1 = (n : ℝ) * p 1 - j := by
        simp [b, mul_sub, mul_div_cancel₀, hnreal.ne']
      change |(n : ℝ) * (p - b) 1| ≤ _
      rw [heq]
      exact (le_max_right _ _).trans hd'
  · have hbnd : ‖p - b + r • (lam • swapCLM) (p - b)‖ ≤ (1 / 2 : ℝ) / n := by
      apply norm_le_of_scaled_coordinates hnreal (by norm_num)
      intro k
      fin_cases k
      · convert hi using 1
        congr 1
        simp [b, swapCLM, swapLinear, Matrix.vecHead, Matrix.vecTail]
        field_simp
      · convert hj using 1
        congr 1
        simp [b, swapCLM, swapLinear, Matrix.vecHead, Matrix.vecTail]
        field_simp
    convert hbnd using 1
    ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.hyperbolic_lattice_model := @_root_.OAI.RuledApproximation.hyperbolic_lattice_model
