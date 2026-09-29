-- Prove2me | solution 1 for Leopoldt.zpRankBelow_le_of_continuous_injective
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:40:21.47109+00:00
-- url     : https://prove2.me/submissions/6118735f-b4f9-4ae9-aaf5-fbf0b0e7bb27

import Definitions.Def_LeopoldtDefect

open Leopoldt

theorem solution (p : ℕ) [Fact p.Prime]
    {G G' : Type*} [CommGroup G] [TopologicalSpace G]
    [CommGroup G'] [TopologicalSpace G'] {b b' : ℕ}
    (f : G →* G') (hf : Function.Injective f) (hc : Continuous f)
    {H : Subgroup G} {H' : Subgroup G'}
    (hmap : ∀ g ∈ H, f g ∈ H') (hb : b ≤ b') :
    zpRankBelow p b H ≤ zpRankBelow p b' H' := by
  apply csSup_le_csSup' ⟨b', fun n hn => hn.1⟩
  rintro n ⟨hn, g, hg, hcont, hrange⟩
  refine ⟨hn.trans hb, f.comp g, hf.comp hg, hc.comp hcont, ?_⟩
  intro x
  exact hmap (g x) (hrange x)
