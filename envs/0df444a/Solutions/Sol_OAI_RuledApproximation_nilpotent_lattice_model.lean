-- Prove2me | solution 1 for OAI.RuledApproximation.nilpotent_lattice_model
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:10:46.026486+00:00
-- url     : https://prove2.me/submissions/a4287cfd-faad-45c4-920d-4cb9bc8764bd

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean:L86-L135
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.nilpotent_lattice_model. The node keeps its source
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
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Theorems.Thm_OAI_RuledApproximation_asymmetric_lattice_cover

-- ---- from OAI.Geometry.RuledCovering.Lattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Sliding rows have no shear bound. This is the local nilpotent model. -/
theorem sliding_rows_cover (d : ℝ) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + d * j)| ≤ 1 / 2 ∧
      |u₂ - (j : ℝ)| ≤ 1 / 2 := by
  simpa using asymmetric_lattice_cover d 0 (by simp) (by simp) u₁ u₂

end RuledApproximation

end

end OAI

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

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.NilpotentLattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A sliding-row lattice for every real shear; the retained radius is finite
but no smallness of the derivative is imposed. -/
theorem nilpotent_lattice_model (d : ℝ) :
    LatticeModel (d • shearCLM) 1 ((1+|d|)/2) := by
  intro n hn p r hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨i,j,hi,hj⟩ := sliding_rows_cover (r*d)
    ((n:ℝ)*p 0 + r*d*((n:ℝ)*p 1)) ((n:ℝ)*p 1)
  have hrd : |r*d| ≤ |d| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hr (abs_nonneg d)
  have hd0 : |(n:ℝ)*p 0-i| ≤ (1+|d|)/2 := by
    have heq : (n:ℝ)*p 0-i =
        ((n:ℝ)*p 0+r*d*((n:ℝ)*p 1)-(i+r*d*j))-r*d*((n:ℝ)*p 1-j) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by
      rw [abs_mul]
      have hm := mul_le_mul hrd hj (abs_nonneg _) (abs_nonneg d)
      linarith)
  let b : Coordinates := ![(i:ℝ)/n,(j:ℝ)/n]
  let : NeZero n := ⟨hn.ne'⟩
  have hb : b ∈ coordinateGrid n := by
    apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
    intro k
    fin_cases k
    · exact ⟨i, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
    · exact ⟨j, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
  refine ⟨b,hb,?_,?_⟩
  · rw [dist_eq_norm, norm_sub_rev]
    apply norm_le_of_scaled_coordinates hnR (by positivity)
    intro k
    fin_cases k
    · simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hd0
    · have hj' : |(n:ℝ)*p 1-j| ≤ (1+|d|)/2 := by linarith [abs_nonneg d]
      simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hj'
  · have hbnd : ‖p-b+r • (d • shearCLM) (p-b)‖ ≤ (1/2:ℝ)/n := by
      apply norm_le_of_scaled_coordinates hnR (by norm_num)
      intro k
      fin_cases k
      · convert hi using 1
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
        field_simp
        ring
      · convert hj using 1
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
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


theorem solution : type_of% @_root_.OAI.RuledApproximation.nilpotent_lattice_model := @_root_.OAI.RuledApproximation.nilpotent_lattice_model
