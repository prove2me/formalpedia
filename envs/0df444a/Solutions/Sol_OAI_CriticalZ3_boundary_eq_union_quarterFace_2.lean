-- Prove2me | solution 2 for OAI.CriticalZ3.boundary_eq_union_quarterFace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:23:32.756323+00:00
-- url     : https://prove2.me/submissions/f9b645e9-d969-4654-b328-cf24ee540a54

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean:L48-L64
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.boundary_eq_union_quarterFace. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Theorems.Thm_OAI_CriticalZ3_quarterFace_subset_boundary

-- ---- from OAI.Probability.CriticalZ3.QuarterFaces ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

universe uE uI uV uW

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

theorem boundary_eq_union_quarterFace (c : Vertex) (n : ℕ) :
    cubeBoundary c n = ⋃ f : FaceIndex, QuarterFace c n f := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx,i,hi⟩
    rw [Set.mem_iUnion]
    let signs : Fin 3 → Bool := fun j => decide (c j ≤ x j)
    refine ⟨(i,signs),?_,?_⟩
    · change x i = c i + (if signs i then (n : ℤ) else -(n : ℤ))
      by_cases h : c i ≤ x i <;> simp [signs,h]
      all_goals rcases hi with hi | hi <;> omega
    · intro j _
      have hh := (mem_cube.mp hx) j
      change if signs j then c j ≤ x j ∧ x j ≤ c j + (n : ℤ)
        else c j - (n : ℤ) ≤ x j ∧ x j ≤ c j
      by_cases h : c j ≤ x j <;> simp [signs,h]
      all_goals omega
  · exact Set.iUnion_subset (quarterFace_subset_boundary c n)

namespace SignedSymmetry

end SignedSymmetry

end CriticalZ3

namespace ProductCylinder

end ProductCylinder

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory Classical
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.boundary_eq_union_quarterFace := @_root_.OAI.CriticalZ3.boundary_eq_union_quarterFace
