-- Prove2me | solution 1 for OAI.RuledApproximation.coordinates_closedBall_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:30:25.799764+00:00
-- url     : https://prove2.me/submissions/564ee487-5c4c-4a8a-a283-a3267a3296d6

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Frames.lean:L57-L87
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.coordinates_closedBall_parallelogram. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames

-- ---- from OAI.Geometry.RuledCovering.Frames ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma coordinates_closedBall (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    closedBall b a = Set.pi univ (fun i => Icc (b i - a) (b i + a)) := by
  ext x
  simp only [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha, Real.norm_eq_abs,
    Pi.sub_apply, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
  constructor <;> intro h i <;> obtain ⟨h₁, h₂⟩ := h i <;> constructor <;> linarith

lemma coordinates_closedBall_parallelogram (b : Coordinates) {a : ℝ} (ha : 0 < a) :
    IsParallelogram (closedBall b a) := by
  let u : Coordinates := ![2*a, 0]
  let v : Coordinates := ![0, 2*a]
  refine ⟨![b 0 - a, b 1 - a], u, v, ?_, ?_⟩
  · have heq : (![u, v] : Fin 2 → Coordinates) =
        fun i => (2 * a) • Pi.basisFun ℝ (Fin 2) i := by
      funext i
      ext j
      fin_cases i <;> fin_cases j <;> simp [u, v, Pi.basisFun_apply]
    rw [heq]
    exact (Pi.basisFun ℝ (Fin 2)).linearIndependent.units_smul
      (fun _ => Units.mk0 (2 * a) (by positivity))
  · rw [coordinates_closedBall b ha.le]
    ext x
    simp only [Set.mem_pi, mem_univ, true_implies, mem_Icc, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨(x 0 - (b 0 - a)) / (2*a), ?_, (x 1 - (b 1 - a)) / (2*a), ?_, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 0).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 0).2]
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 1).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 1).2]
      · ext i
        fin_cases i <;> simp [u, v, (by positivity : 2*a ≠ 0)]
    · rintro ⟨s, hs, t, ht, rfl⟩ i
      fin_cases i <;> simp [u, v] <;> constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.coordinates_closedBall_parallelogram := @_root_.OAI.RuledApproximation.coordinates_closedBall_parallelogram
