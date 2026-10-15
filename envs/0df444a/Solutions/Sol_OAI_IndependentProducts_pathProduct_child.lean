-- Prove2me | solution 1 for OAI.IndependentProducts.pathProduct_child
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:59:31.522526+00:00
-- url     : https://prove2.me/submissions/a5d3fb12-a676-45e1-9eed-9504f13a0fee

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/PathMoments.lean:L189-L208
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.pathProduct_child. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments

-- ---- from OAI.Analysis.ProductSpaces.PathMoments ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section CoordinateProducts

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

lemma pathProduct_child (v : Vertex) (n : ℕ) (ω : Sample) :
    pathProduct (child v n) ω = pathProduct v ω * ω (childEdge v n) := by
  let e : Fin (v.length + 1) ≃ Fin (child v n).length := finCongr (child_length v n).symm
  have he := Fintype.prod_equiv e
    (fun i => ω (pathPrefix (child v n) (e i)))
    (fun j => ω (pathPrefix (child v n) j)) (fun _ => rfl)
  change _ = (∏ j, ω (pathPrefix v j)) * _
  rw [show pathProduct (child v n) ω = ∏ i : Fin (v.length + 1),
    ω (pathPrefix (child v n) (e i)) from he.symm, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    congr 1
    apply Subtype.ext
    change (child v n).take (j.val + 1) = v.take (j.val + 1)
    exact List.take_append_of_le_length (by omega)
  · congr 1
    apply Subtype.ext
    change (child v n).take (v.length + 1) = child v n
    rw [← child_length, List.take_length]

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end ChildMoments
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι

theorem solution (v : Vertex) (n : ℕ) (ω : Sample) :
    pathProduct (child v n) ω = pathProduct v ω * ω (childEdge v n) := by
  first
    | exact OAI.IndependentProducts.pathProduct_child v n ω
    | exact OAI.IndependentProducts.pathProduct_child
    | (apply OAI.IndependentProducts.pathProduct_child <;> assumption)
    | (intros; apply OAI.IndependentProducts.pathProduct_child <;> assumption)
