-- Prove2me | solution 1 for LovaszLocalLemma.propertyB_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:34:09.618797+00:00
-- url     : https://prove2.me/submissions/ea6ad966-437e-40e9-a1e2-98f2335420c6

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Definitions.Def_LovaszLocalLemma_Solution
public import Theorems.Thm_LocalLemma_propertyB_regular


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LovaszLocalLemma
namespace LovaszLocalLemma
theorem _root_.solution {V : Type*} [DecidableEq V] (H : Finset (Finset V)) {k : ℕ}
    (h9 : 9 ≤ k) (hk : ∀ e ∈ H, e.card = k) (hdeg : ∀ v, (H.filter fun e => v ∈ e).card ≤ k) :
    ∃ c : V → Bool, ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y :=
  LocalLemma.propertyB_regular H h9 hk hdeg
end LovaszLocalLemma
