-- Prove2me | solution 1 for GlobalTheory.dense_interior_of_interior_frontier_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:01.185057+00:00
-- url     : https://prove2.me/submissions/8aa02892-d14b-402c-85bd-2eba96d1fef8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

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
variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
namespace GlobalTheory
theorem _root_.solution {S : Set Y} (hS : Dense S)
    (h : interior (frontier S) = ∅) : Dense (interior S) := by
  have h1 : frontier S = (interior S)ᶜ := by
    rw [frontier, hS.closure_eq, Set.compl_eq_univ_diff]
  rwa [h1, interior_eq_empty_iff_dense_compl, compl_compl] at h
end GlobalTheory
