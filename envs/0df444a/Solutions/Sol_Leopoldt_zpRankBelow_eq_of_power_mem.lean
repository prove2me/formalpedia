-- Prove2me | solution 1 for Leopoldt.zpRankBelow_eq_of_power_mem
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:04:03.940624+00:00
-- url     : https://prove2.me/submissions/c80244f4-70d4-42c4-a4bf-84667d41f4da

import Definitions.Def_LeopoldtDefect
import Theorems.Thm_Leopoldt_zpRankBelow_mono_subgroup

open Leopoldt

theorem solution (p : ℕ) [Fact p.Prime]
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (b : ℕ) {H H' : Subgroup G} (hsub : H' ≤ H)
    (m : ℕ) (hm : m ≠ 0) (hpow : ∀ x ∈ H, x ^ m ∈ H') :
    zpRankBelow p b H' = zpRankBelow p b H := by
  apply le_antisymm (zpRankBelow_mono_subgroup p b hsub)
  apply csSup_le_csSup' ⟨b, fun n hn => hn.1⟩
  rintro n ⟨hn, g, hg, hc, hrange⟩
  refine ⟨hn, g.comp (powMonoidHom m), hg.comp (pow_left_injective hm),
    hc.comp (continuous_pow m), ?_⟩
  intro x
  change g (x ^ m) ∈ H'
  rw [map_pow]
  exact hpow (g x) (hrange x)
