-- Prove2me | solution 1 for OAI.DoublingHilbert.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:56:53.473745+00:00
-- url     : https://prove2.me/submissions/780bafe7-1d8c-4259-909b-00e72b6094df

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Main.lean:L56-L65
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.DoublingHilbert.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_DoublingHilbert_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Theorems.Thm_OAI_DoublingHilbert_constructedSet_cover
import Theorems.Thm_OAI_DoublingHilbert_no_scaled_embedding

-- ---- from OAI.Geometry.DoublingHilbert.Main ----
namespace OAI

/-! A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open Metric

section Nonembedding
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end Nonembedding
end DoublingHilbert

namespace DoublingHilbert

/-- A single fixed subset, independent of dimension and distortion. -/
theorem main : ∃ S : Set RealL2,
    DoublingAtMost S 76800 ∧
      ∀ k : ℕ, 0 < k → ¬ AdmitsBiLipschitzEmbedding S k := by
  refine ⟨constructedSet, ?_, ?_⟩
  · intro x r hr
    exact constructedSet_cover x hr
  · intro k _ hEmbedding
    obtain ⟨f, a, ha, D, hD, hf⟩ := hEmbedding
    exact no_scaled_embedding f ha hD hf

end DoublingHilbert

end OAI

-- ---- mission target ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology

theorem solution : ∃ S : Set RealL2,
    DoublingAtMost S 76800 ∧
      ∀ k : ℕ, 0 < k → ¬ AdmitsBiLipschitzEmbedding S k := by
  first
    | exact OAI.DoublingHilbert.main
    | (apply OAI.DoublingHilbert.main <;> assumption)
    | (intros; apply OAI.DoublingHilbert.main <;> assumption)
