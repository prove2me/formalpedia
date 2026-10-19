-- Prove2me | solution 2 for OAI.CriticalZ3.quarterFace_subset_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:21:12.08686+00:00
-- url     : https://prove2.me/submissions/88d92e06-d658-40f6-9637-9218d6ce38f2

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean:L32-L46
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.quarterFace_subset_boundary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

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

theorem quarterFace_subset_boundary (c : Vertex) (n : ℕ) (f : FaceIndex) :
    QuarterFace c n f ⊆ cubeBoundary c n := by
  intro x hx
  refine ⟨?_,f.1,?_⟩
  · rw [mem_cube]
    intro i
    by_cases hi : i = f.1
    · subst i
      rw [hx.1]
      cases f.2 f.1 <;> simp
      omega
    · have h := hx.2 i hi
      cases hf : f.2 i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · rw [hx.1]
    cases f.2 f.1 <;> simp [sub_eq_add_neg]

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


theorem solution : type_of% @_root_.OAI.CriticalZ3.quarterFace_subset_boundary := @_root_.OAI.CriticalZ3.quarterFace_subset_boundary
