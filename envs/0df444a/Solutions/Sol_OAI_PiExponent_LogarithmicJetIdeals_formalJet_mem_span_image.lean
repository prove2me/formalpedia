-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_mem_span_image
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T08:07:10.72411+00:00
-- url     : https://prove2.me/submissions/0892b1dc-be80-4a4c-93a1-ae84e0c3ccdd

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ)
    (S : Set (MvPolynomial (Fin (m + 1)) ℂ))
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ Ideal.span S) :
    formalJet c Q ∈ Ideal.span (formalJet c '' S) := by
  have hmap : formalJet c Q ∈ Ideal.map (formalJet c) (Ideal.span S) :=
    Ideal.mem_map_of_mem (formalJet c) hQ
  rw [Ideal.map_span] at hmap
  exact hmap