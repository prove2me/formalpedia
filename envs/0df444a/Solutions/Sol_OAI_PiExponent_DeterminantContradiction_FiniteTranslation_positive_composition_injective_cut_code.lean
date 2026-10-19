-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_injective_cut_code
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:25:36.031261+00:00
-- url     : https://prove2.me/submissions/4841b943-0b51-4f1c-ade7-f356d30ee9df

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_degenerate_positive_composition_cut_code
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_nontrivial_positive_composition_cut_code

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by
  classical
  by_cases hdeg : q = 0 ∨ k = 0 ∨ q = 1
  · exact degenerate_positive_composition_cut_code q k hdeg
  · have hq : 0 < q := by omega
    have hk : 0 < k := by omega
    have hqne : q ≠ 1 := by omega
    exact nontrivial_positive_composition_cut_code q k hq hk hqne