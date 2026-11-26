-- Prove2me | solution 1 for LovaszLocalLemma.ramsey_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:31:27.415908+00:00
-- url     : https://prove2.me/submissions/07b79659-3fdd-418a-b85c-9855346efc31

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Definitions.Def_LovaszLocalLemma_Solution
public import Theorems.Thm_LocalLemma_ramsey_lower


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LovaszLocalLemma
namespace LovaszLocalLemma
theorem _root_.solution {n k : ℕ}
    (h : 2 * Real.exp 1 * ((k.choose 2 * n.choose (k - 2) : ℕ) + 1) ≤ 2 ^ k.choose 2) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  LocalLemma.ramsey_lower h
end LovaszLocalLemma
