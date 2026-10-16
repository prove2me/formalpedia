-- Prove2me | solution 1 for OAI.Paper256.interior_line_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:52:44.563314+00:00
-- url     : https://prove2.me/submissions/739d9490-b64c-4878-8c9e-9d2a79a34bb4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilKernel.lean:L27-L41
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.interior_line_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation

-- ---- from OAI.Analysis.HyperbolicCones.PencilKernel ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

theorem interior_line_pair {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} {e : V} (he : e ∈ interior K) (x : V) :
    ∃ ε : ℝ, 0 < ε ∧ e + ε • x ∈ K ∧ e - ε • x ∈ K := by
  have hp : Tendsto (fun t : ℝ => e + t • x) (𝓝 0) (𝓝 e) := by
    have h : Continuous (fun t : ℝ => e + t • x) := by fun_prop
    simpa using h.tendsto (0 : ℝ)
  have hm : Tendsto (fun t : ℝ => e - t • x) (𝓝 0) (𝓝 e) := by
    have h : Continuous (fun t : ℝ => e - t • x) := by fun_prop
    simpa using h.tendsto (0 : ℝ)
  have hh := (hp.eventually (mem_interior_iff_mem_nhds.mp he)).and
    (hm.eventually (mem_interior_iff_mem_nhds.mp he))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨r / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder


theorem solution.{u} : type_of% @_root_.OAI.Paper256.interior_line_pair.{u} := @_root_.OAI.Paper256.interior_line_pair.{u}
