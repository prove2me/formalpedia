-- Prove2me | solution 1 for Nock.Verb.runTraceProgram_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:43.430813+00:00
-- url     : https://prove2.me/submissions/40c24e6e-ae90-47a9-9c2e-75011a9c2267

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
public import Theorems.Thm_Nock_Verb_runTrace_traceOf
public import Theorems.Thm_Nock_Verb_runTrace_complete
public import Theorems.Thm_Nock_Verb_runTrace_adjacent_nockCheck
public import Theorems.Thm_Nock_Verb_runTrace_final_edge

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {fuel : Nat} {subject formula : Noun} {T : List Verb}
    (h : runTraceProgram fuel subject formula = some T) :
    TraceOf (program subject formula) T ∧ Complete T ∧ AdjNockCheck T ∧
      (∃ w, T.getLast? = some w ∧ (isTerminal w = true ∨ NockCheck w none = true)) :=
  ⟨runTrace_traceOf h, runTrace_complete h, runTrace_adjacent_nockCheck h, runTrace_final_edge h⟩
end Nock.Verb
