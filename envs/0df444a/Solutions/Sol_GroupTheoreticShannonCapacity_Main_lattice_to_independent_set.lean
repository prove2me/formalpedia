-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Main.lattice_to_independent_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:07.145304+00:00
-- url     : https://prove2.me/submissions/9362a42b-a61d-4724-9d62-93899ef45fe4

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_matrixToIndependentSet


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
namespace GroupTheoreticShannonCapacity.Main
theorem _root_.solution (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ) (p q : ℕ) [NeZero p] (hq : 0 < q)
    (hAB : A * B = p • 1)
    (hMinDist : minDistance n (latticeOfMatrix n (A.map (↑· : ℤ → ℝ))) ≥ q) :
    ∃ S : AddSubgroup (Fin n → ZMod p),
      (strongPower (fractionGraph p q) n).IsIndepSet (S : Set (Fin n → ZMod p)) ∧
      Nat.card S ≥ Int.natAbs B.det :=
  matrixToIndependentSet n A B p q hq hAB hMinDist
end GroupTheoreticShannonCapacity.Main
