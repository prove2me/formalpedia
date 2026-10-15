-- Prove2me | solution 1 for OAI.DoublingHilbert.near_lexicographic_maximum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:21:25.294046+00:00
-- url     : https://prove2.me/submissions/ddc463b9-7172-435c-8392-ea1b72e59024

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Extremal.lean:L11-L39
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.near_lexicographic_maximum. The node keeps its source
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

-- ---- from OAI.Geometry.DoublingHilbert.Extremal ----
namespace OAI

/-! Compact lexicographic extrema and quantitative second-moment estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
/-- Near a compact lexicographic maximum, the second coordinate has a uniform upper bound. -/
theorem near_lexicographic_maximum
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, A - δ < p.1 → p.2 ≤ B + ε := by
  let bad : Set (ℝ × ℝ) := K ∩ {p | B + ε ≤ p.2}
  have hbcompact : IsCompact bad :=
    hK.inter_right (isClosed_le continuous_const continuous_snd)
  by_cases hb : bad.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hbcompact.exists_isMaxOn hb continuous_fst.continuousOn
    have hpA : p.1 < A := by
      apply lt_of_le_of_ne (hfirst p hp.1)
      intro heq
      have hpB := hsecond p hp.1 heq
      have hpB' : B + ε ≤ p.2 := hp.2
      linarith
    refine ⟨A - p.1, sub_pos.mpr hpA, ?_⟩
    intro q hq hqA
    by_contra hqB
    have hqb : q ∈ bad := ⟨hq, (not_le.mp hqB).le⟩
    have := hmax hqb
    dsimp at this
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p hp _
    by_contra h
    exact hb ⟨p, hp, (not_le.mp h).le⟩

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
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {A B : ℝ}
    (hfirst : ∀ p ∈ K, p.1 ≤ A)
    (hsecond : ∀ p ∈ K, p.1 = A → p.2 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, A - δ < p.1 → p.2 ≤ B + ε := by
  first
    | exact OAI.DoublingHilbert.near_lexicographic_maximum hK hfirst hsecond hε
    | exact OAI.DoublingHilbert.near_lexicographic_maximum
    | (apply OAI.DoublingHilbert.near_lexicographic_maximum <;> assumption)
    | (intros; apply OAI.DoublingHilbert.near_lexicographic_maximum <;> assumption)
