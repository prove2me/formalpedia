-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Main.construction_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:11.692797+00:00
-- url     : https://prove2.me/submissions/f0fc10c3-e181-4077-9c52-f6a88afc4532

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_gives_shannon_bound


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
namespace GroupTheoreticShannonCapacity.Main
theorem _root_.solution (n k b r s : ℕ) [NeZero n]
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    have pVal := Construction.p n k b r s
    have qVal := Construction.q n k b r s
    ∃ p' q' : ℕ, ∃ (_ : NeZero p') (_ : 0 < q'),
      (p' : ℚ) = pVal ∧ (q' : ℚ) = qVal ∧
      shannonCapacity (fractionGraph p' q') ≥ (p' : ℝ) ^ (1 / (n : ℝ)) :=
  construction_gives_shannon_bound n k b r s hk hb hrb
end GroupTheoreticShannonCapacity.Main
