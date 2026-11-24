-- Prove2me | solution 1 for GlobalTheory.CharpolyPow.det_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:52.263222+00:00
-- url     : https://prove2.me/submissions/223a0100-21fe-45c8-b35e-18818f391df6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Theorems.Thm_GlobalTheory_CharpolyPow_card_roots_charpoly
import Theorems.Thm_GlobalTheory_CharpolyPow_det_aeval_prod

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) k) (q : k[X]) :
    (aeval M q).det = (M.charpoly.roots.map (fun z => eval z q)).prod := by
  set m := Multiset.card q.roots
  set c := q.leadingCoeff * (-1) ^ m
  have hq : q = C c * (q.roots.map (fun a => C a - X)).prod := by
    have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    have hneg : (q.roots.map (fun a => C a - X)).prod
        = (-1) ^ m * (q.roots.map (fun a => X - C a)).prod := by
      have : (fun a : k => C a - X) = fun a => (-1) * (X - C a) := by
        funext a; ring
      rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    rw [hneg, C_mul, C_pow, C_neg, C_1]
    calc q = C q.leadingCoeff * (q.roots.map (fun a => X - C a)).prod := hsplit.symm
      _ = C q.leadingCoeff * (-1) ^ m * ((-1) ^ m * (q.roots.map (fun a => X - C a)).prod) := by
        rw [← mul_assoc, mul_assoc (C q.leadingCoeff), ← pow_add, ← two_mul, pow_mul]
        simp
  have hcard : Multiset.card M.charpoly.roots = n := card_roots_charpoly M
  conv_lhs => rw [hq]
  conv_rhs => rw [hq]
  rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.det_smul,
    Fintype.card_fin, det_aeval_prod]
  simp only [eval_mul, eval_C]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]
end GlobalTheory.CharpolyPow
