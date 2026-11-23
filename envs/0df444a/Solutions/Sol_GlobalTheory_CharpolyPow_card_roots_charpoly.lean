-- Prove2me | solution 1 for GlobalTheory.CharpolyPow.card_roots_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:39.742408+00:00
-- url     : https://prove2.me/submissions/4608e3ca-fa60-45f7-ad15-7f62e73f207c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CharpolyPow
variable {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
namespace GlobalTheory.CharpolyPow
theorem _root_.solution (M : Matrix (Fin n) (Fin n) k) : Multiset.card M.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
end GlobalTheory.CharpolyPow
