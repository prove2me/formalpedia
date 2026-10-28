-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ext
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:14:41.503177+00:00
-- url     : https://prove2.me/submissions/82bc6196-0f7c-425c-887e-517a962388e7

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_MarkovProcess_Semigroup_Basic

open Filter Topology
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem solution {S T : StronglyContinuousContractionSemigroup E}
    (h : ∀ t, S t = T t) : S = T := by
  cases S; cases T
  congr
  funext t
  exact h t
