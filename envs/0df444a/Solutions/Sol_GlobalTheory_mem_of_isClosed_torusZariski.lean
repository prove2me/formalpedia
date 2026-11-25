-- Prove2me | solution 1 for GlobalTheory.mem_of_isClosed_torusZariski
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:35.987209+00:00
-- url     : https://prove2.me/submissions/26724b54-a42d-4002-b31c-ffb72909dc00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_isClosed_torusZariski_iff
import Theorems.Thm_GlobalTheory_torusEval_eq_zero_of_forall_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
variable [IsDomain R]
namespace GlobalTheory
theorem _root_.solution {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    {t : Multiplicative X →* Rˣ}
    (ht : ∀ x : Multiplicative X, (∀ s ∈ H, s x = 1) → t x = 1) : t ∈ H := by
  obtain ⟨S, hS⟩ := (isClosed_torusZariski_iff _).1 hH
  exact (hS t).2 fun f hf => torusEval_eq_zero_of_forall_char H (fun s hs => (hS s).1 hs f hf) ht
end GlobalTheory
