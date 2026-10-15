-- Prove2me | solution 1 for OAI.DoublingHilbert.lexicographic_affine_barrier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:22:43.244453+00:00
-- url     : https://prove2.me/submissions/a424f04d-4305-4543-add0-77b9754947b3

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Extremal.lean:L58-L76
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.lexicographic_affine_barrier. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Theorems.Thm_OAI_DoublingHilbert_near_lexicographic_maximum

-- ---- from OAI.Geometry.DoublingHilbert.Extremal ----
namespace OAI

/-! Compact lexicographic extrema and quantitative second-moment estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
/-- An affine barrier bounds the second coordinate in terms of the first-coordinate deficit. -/
theorem lexicographic_affine_barrier
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B M : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    (hbound : ∀ p ∈ K, p.2 ≤ M) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1) := by
  obtain ⟨δ, hδ, hnear⟩ := near_lexicographic_maximum hK hfirst hsecond hε
  refine ⟨M / δ, div_nonneg hM hδ.le, ?_⟩
  intro p hp
  have hdef : 0 ≤ A - p.1 := sub_nonneg.mpr (hfirst p hp)
  by_cases hclose : A - δ < p.1
  · exact (hnear p hp hclose).trans (le_add_of_nonneg_right (by positivity))
  · have hgap : δ ≤ A - p.1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hgap (div_nonneg hM hδ.le)
    have heq : M / δ * δ = M := div_mul_cancel₀ _ hδ.ne'
    have hpm := hbound p hp
    linarith

open MeasureTheory
open scoped BigOperators

section Moments

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

end Moments

end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology

theorem solution
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B M : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    (hbound : ∀ p ∈ K, p.2 ≤ M) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1) := by
  first
    | exact OAI.DoublingHilbert.lexicographic_affine_barrier hK hfirst hsecond hbound hB hM hε
    | exact OAI.DoublingHilbert.lexicographic_affine_barrier
    | (apply OAI.DoublingHilbert.lexicographic_affine_barrier <;> assumption)
    | (intros; apply OAI.DoublingHilbert.lexicographic_affine_barrier <;> assumption)
