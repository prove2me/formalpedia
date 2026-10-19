-- Prove2me | solution 2 for OAI.CriticalZ3.quarterFace_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:26:31.167849+00:00
-- url     : https://prove2.me/submissions/a048d7b5-f7d2-4d68-a96a-c6ad85d5d63d

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean:L131-L172
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.quarterFace_preimage. The node keeps its source
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

namespace SignedSymmetry

end SignedSymmetry

theorem quarterFace_preimage (c : Vertex) (n : ℕ) (f : FaceIndex) :
    (faceSymmetry c f).vertex ⁻¹' QuarterFace c n f = QuarterFace 0 n canonicalFace := by
  ext x
  simp only [Set.mem_preimage,QuarterFace,Set.mem_ofPred_eq,canonicalFace,
    Pi.zero_apply,zero_add,ite_true]
  have hn : (faceSymmetry c f).vertex x f.1 =
      c f.1 + if f.2 f.1 then x 0 else -x 0 := by
    simp [faceSymmetry,SignedSymmetry.vertex]
  rw [hn]
  have hnormal : (c f.1 + (if f.2 f.1 then x 0 else -x 0) =
      c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ))) ↔ x 0 = (n : ℤ) := by
    cases f.2 f.1 <;> simp
  rw [hnormal]
  apply and_congr_right
  intro _
  have hi (i : Fin 3) :
      (if f.2 i then c i ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i) ↔
      (0 ≤ x (Equiv.swap f.1 0 i) ∧ x (Equiv.swap f.1 0 i) ≤ (n : ℤ)) := by
    change (if f.2 i then c i ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i) ↔ _
    cases f.2 i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  simp_rw [hi]
  constructor
  · intro h i hi
    have hh := h (Equiv.swap f.1 0 i)
    simp only [Equiv.swap_apply_self] at hh
    apply hh
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self,Equiv.swap_apply_left] at this
    exact hi this
  · intro h i hi
    apply h
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
    exact hi this

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


theorem solution : type_of% @_root_.OAI.CriticalZ3.quarterFace_preimage := @_root_.OAI.CriticalZ3.quarterFace_preimage
