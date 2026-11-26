-- Prove2me | solution 1 for LovaszLocalLemma.propertyB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:32:29.157077+00:00
-- url     : https://prove2.me/submissions/eaf76d75-09f0-4387-a5d2-267f0c075a09

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Definitions.Def_LovaszLocalLemma_Solution
public import Theorems.Thm_LocalLemma_propertyB


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LovaszLocalLemma
namespace LovaszLocalLemma
theorem _root_.solution {V : Type*} [DecidableEq V] (H : Finset (Finset V)) {k d : ℕ}
    (hk : ∀ e ∈ H, e.card = k)
    (hd : ∀ e ∈ H, (H.filter fun f => f ≠ e ∧ ¬ Disjoint e f).card ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ (k - 1)) :
    ∃ c : V → Bool, ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y :=
  LocalLemma.propertyB H hk hd h
end LovaszLocalLemma
