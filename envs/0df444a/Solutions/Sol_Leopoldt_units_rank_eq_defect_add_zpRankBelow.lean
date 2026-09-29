-- Prove2me | solution 1 for Leopoldt.units_rank_eq_defect_add_zpRankBelow
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:24:42.222241+00:00
-- url     : https://prove2.me/submissions/7382d37c-bccd-4da7-ad77-ec168086bc6f

import Theorems.Thm_Leopoldt_zpRankBelow_unitClosure_le_units_rank

open NumberField Leopoldt

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    Units.rank K = defect p K + zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) := by
  have h := zpRankBelow_unitClosure_le_units_rank p K
  unfold defect
  omega
