-- Prove2me | solution 1 for GraphonGames.Existence.proposition_3_1_aggregate_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:51:21.361036+00:00
-- url     : https://prove2.me/submissions/9af3432a-c776-430e-9a56-3e72911fb125

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting
import Theorems.Thm_GraphonGames_Stability_proposition_3_1_aggregate_exists_unique

open MeasureTheory
open scoped ENNReal

open GraphonGames.Existence

theorem solution (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : Asm1 b μ0 cα cz) (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1) (α : I → ℝ) (hα : MemLp α 2 volume) :
    ∃ z : I → ℝ, IsAggregate w b α z ∧ ∀ z' : I → ℝ, IsAggregate w b α z' → z' =ᵐ[volume] z :=
  GraphonGames.Stability.proposition_3_1_aggregate_exists_unique b μ0 cα cz h1 w hw hW α hα
