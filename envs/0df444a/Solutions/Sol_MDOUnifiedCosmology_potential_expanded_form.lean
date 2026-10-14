-- Prove2me | solution 1 for MDOUnifiedCosmology.potential_expanded_form
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:32.945683+00:00
-- url     : https://prove2.me/submissions/e0901b72-2b53-405c-9fc3-7296dc1149e2

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (A φc m α : ℝ) (hφc : φc ≠ 0) (φ : ℝ) :
    potential A φc m α φ =
      1 / 2 * effMassSq A φc m * φ ^ 2 + effCoupling A φc α / 4 * φ ^ 4 + A ^ 4 := by
  unfold potential V1 V2 effMassSq effCoupling
  field_simp
  ring


