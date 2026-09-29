-- Prove2me | solution 1 for Leopoldt.zpRankBelow_mono_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:43:11.745146+00:00
-- url     : https://prove2.me/submissions/9b257a69-9853-4ef1-8e63-64290d2b8d73

import Definitions.Def_LeopoldtDefect

open NumberField IsDedekindDomain Leopoldt

theorem solution (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    [TopologicalSpace G] {b b' : ℕ} (h : b ≤ b') (H : Subgroup G) :
    zpRankBelow p b H ≤ zpRankBelow p b' H := by
  apply csSup_le_csSup' ⟨b', fun n hn => hn.1⟩
  rintro n ⟨hn, hf⟩
  exact ⟨hn.trans h, hf⟩
