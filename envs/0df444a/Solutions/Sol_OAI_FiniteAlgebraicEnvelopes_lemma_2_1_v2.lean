-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_2_1_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T19:43:21.184851+00:00
-- url     : https://prove2.me/submissions/cc22050c-dc36-4790-864c-318753f3925d

import Mathlib
import Definitions.Def_BooneHigman
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_2_1_construction_v2
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_2_1_decidability_v2

universe u

open OAI.FiniteAlgebraicEnvelopes in
theorem solution {H : Type u} [Group H] [Group.FG H] (hH : HasDecidableWordProblem H) :
    ∃ (K : Type u) (_ : Group K), Group.FG K ∧ HasDecidableWordProblem K ∧
      ∃ (ι : H × H →* K), Function.Injective ι ∧
      ∃ s : K, ∀ g : H, ι (g, g) * s * (ι (g, g))⁻¹ * s⁻¹ = ι (g, 1) := by
  obtain ⟨hfg, hinj, hcomm⟩ := OAI.FiniteAlgebraicEnvelopes.lemma_2_1_construction_v2 (H := H)
  exact ⟨_, _, hfg, OAI.FiniteAlgebraicEnvelopes.lemma_2_1_decidability_v2 hH,
    HNNExtension.of, hinj, HNNExtension.t, hcomm⟩
