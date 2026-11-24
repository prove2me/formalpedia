-- Prove2me | solution 1 for GlobalTheory.CharpolyPow.roots_charpoly_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:03:32.368677+00:00
-- url     : https://prove2.me/submissions/a9ace298-0ceb-4731-8229-622d028229ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Theorems.Thm_GlobalTheory_CharpolyPow_det_aeval

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
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ)
    (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  have hinf : Infinite k := IsAlgClosed.instInfinite
  have hcard : Multiset.card (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly (M ^ r)).natDegree := by
    exact IsAlgClosed.card_roots_eq_natDegree
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic (M ^ r)) hcard
  suffices h : Matrix.charpoly (M ^ r) = (((Matrix.charpoly M).roots.map (· ^ r)).map fun a => X - C a).prod by
    rw [h, roots_multiset_prod_X_sub_C]
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  have h1 : Matrix.scalar (Fin n) t - M ^ r = aeval M (C t - X ^ r) := by
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  rw [h1, GlobalTheory.CharpolyPow.det_aeval]
  simp [Function.comp_def]
end GlobalTheory.CharpolyPow
