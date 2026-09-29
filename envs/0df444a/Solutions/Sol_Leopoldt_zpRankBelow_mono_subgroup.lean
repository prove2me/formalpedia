-- Prove2me | solution 1 for Leopoldt.zpRankBelow_mono_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:43:12.961531+00:00
-- url     : https://prove2.me/submissions/882a4673-77a3-451d-aadf-01e2fc964e75

import Definitions.Def_LeopoldtDefect

open NumberField IsDedekindDomain Leopoldt

theorem solution (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    [TopologicalSpace G] (b : ℕ) {H H' : Subgroup G} (h : H ≤ H') :
    zpRankBelow p b H ≤ zpRankBelow p b H' := by
  apply csSup_le_csSup' ⟨b, fun n hn => hn.1⟩
  rintro n ⟨hn, f, hi, hc, hf⟩
  exact ⟨hn, f, hi, hc, fun x => h (hf x)⟩
