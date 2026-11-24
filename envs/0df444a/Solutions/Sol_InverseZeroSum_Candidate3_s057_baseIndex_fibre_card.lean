-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s057_baseIndex_fibre_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:33.278786+00:00
-- url     : https://prove2.me/submissions/2ea2bb40-b17a-4005-8946-69086b15c565

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution (a : Fin 8) :
    ((Finset.univ : Finset (Fin 24)).filter
      (fun i => baseIndex i = a)).card = 3 := by
  fin_cases a <;> decide
end InverseZeroSum.Candidate3
