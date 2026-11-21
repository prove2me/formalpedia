-- Prove2me | solution 1 for OAI.HadwigerCounterexample.exists_counterexamples
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T22:16:04.764391+00:00
-- url     : https://prove2.me/submissions/b576b8c9-c8df-408b-a1e1-14f326dfa8ce

import Mathlib
import Definitions.Def_HadwigerMatching_Defs
import Definitions.Def_ListHadwiger
import Theorems.Thm_OAI_HadwigerCounterexample_exists_graphs
import Theorems.Thm_OAI_HadwigerMatching_full_matching_minor_proposition

open OAI.HadwigerMatching OAI.LinearListHadwiger

theorem solution (M : ℕ) : ∃ m : ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧ (connectedMatchingNumber G : ℚ) < (m : ℚ) / 100 ∧
      (hadwigerNumber G : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
      26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧ (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ) ∧
      hadwigerNumber G < G.chromaticNumber.toNat ∧
      G.chromaticNumber ≠ ⊤ ∧ G.chromaticNumber = ↑(G.chromaticNumber.toNat) := by
  obtain ⟨m, hm, G, ha, hc⟩ := OAI.HadwigerCounterexample.exists_graphs M
  have he : 5 ≤ m := (le_max_right ..).trans hm
  have : NeZero m := ⟨by omega⟩
  have hx := OAI.HadwigerMatching.full_matching_minor_proposition (Fin m) G
  dsimp only at hx
  rw [Fintype.card_fin] at hx
  obtain ⟨h1, h2, h3⟩ := hx.2 ha hc he
  have hk : G.chromaticNumber ≠ ⊤ := by
    intro h; have hs := G.chromaticNumber_le_card; simp [h] at hs
  refine ⟨m, hm, G, ha, hc, h1, h2, h3, ?_, hk, ?_⟩
  · exact_mod_cast ((h1.trans h2).trans_le h3)
  exact (ENat.natCast_toNat_eq_self.mpr hk).symm
