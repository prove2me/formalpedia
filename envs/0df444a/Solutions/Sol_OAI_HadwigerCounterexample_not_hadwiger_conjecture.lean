-- Prove2me | solution 1 for OAI.HadwigerCounterexample.not_hadwiger_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T22:16:04.566189+00:00
-- url     : https://prove2.me/submissions/2f2f76f1-5384-4645-952a-5e724268e6bd

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_HadwigerMatching_Defs
import Theorems.Thm_OAI_HadwigerCounterexample_exists_counterexamples

open OAI.LinearListHadwiger

theorem solution :
    ¬ (∀ (m : ℕ) (G : SimpleGraph (Fin m)),
      G.chromaticNumber ≤ ↑(hadwigerNumber G)) := by
  intro h
  obtain ⟨m, hM, G, h1, h2, h3, h4, h5, h6, he, hC⟩ := OAI.HadwigerCounterexample.exists_counterexamples 0
  have ht := h m G
  rw [hC] at ht
  exact h6.not_ge (by exact_mod_cast ht)
