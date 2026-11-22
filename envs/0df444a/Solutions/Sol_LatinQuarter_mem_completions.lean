-- Prove2me | solution 1 for LatinQuarter.mem_completions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:27.658338+00:00
-- url     : https://prove2.me/submissions/71444527-3c2a-454e-bff6-3fba595ff8f1

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_LatinQuarter_Basic

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution {n : ℕ} {P : Finset (Cell n)}
    {L M : Square n} :
    M ∈ completions P L ↔ IsLatin M ∧ Agrees P L M := by
  classical
  simp [completions]
end LatinQuarter
