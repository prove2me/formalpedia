-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_card_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:20:50.509982+00:00
-- url     : https://prove2.me/submissions/a8512a98-56a8-459c-80cc-229db75d1d16

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_positive_composition_injective_cut_code

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) :
    (logMajorantCompositions q k).card ≤ 2 ^ k := by
  obtain ⟨f, hf⟩ :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_injective_cut_code q k
  calc
    (logMajorantCompositions q k).card =
        Fintype.card {a // a ∈ logMajorantCompositions q k} :=
      (Fintype.card_coe (logMajorantCompositions q k)).symm
    _ ≤ Fintype.card (Finset (Fin k)) := Fintype.card_le_of_injective f hf
    _ = 2 ^ k := by simp