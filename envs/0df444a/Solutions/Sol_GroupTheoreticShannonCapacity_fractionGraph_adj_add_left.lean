-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.fractionGraph_adj_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:38:31.188283+00:00
-- url     : https://prove2.me/submissions/fda5c568-a491-4d7a-8cc6-afac15783f44

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_distMod_add_left

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p q : ℕ) [NeZero p] (c u v : ZMod p) :
    (fractionGraph p q).Adj (c + u) (c + v) ↔ (fractionGraph p q).Adj u v := by
  simp only [fractionGraph, distMod_add_left, ne_eq, add_left_cancel_iff]
end GroupTheoreticShannonCapacity
