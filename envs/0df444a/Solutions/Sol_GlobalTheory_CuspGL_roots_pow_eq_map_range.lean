-- Prove2me | solution 1 for GlobalTheory.CuspGL.roots_pow_eq_map_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:23:49.348026+00:00
-- url     : https://prove2.me/submissions/c57ad46d-12a8-493f-ba98-f140e84df623

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPow
import Theorems.Thm_GlobalTheory_CuspGL_map_range_mul_of_periodic
import Theorems.Thm_GlobalTheory_CuspGL_minpoly_natDegree_dvd_iff_pow
import Theorems.Thm_GlobalTheory_CuspGL_roots_minpoly_eq_map_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] [Finite F] (f : F[X]) (m : ℕ) (hf : f.Monic)
    (hi : Irreducible f) (α : AlgebraicClosure F)
    (hα : α ∈ ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots) :
    ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (f ^ m).natDegree).map fun i => α ^ Nat.card F ^ i := by
  rw [Polynomial.map_pow, roots_pow] at hα ⊢
  have h1 := Multiset.mem_of_mem_nsmul hα
  have h2 : aeval α f = 0 := by
    rw [← eval_map_algebraMap]
    exact (mem_roots'.1 h1).2
  have h3 : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi h2 hf
  have hper := (minpoly_natDegree_dvd_iff_pow α _).1 dvd_rfl
  rw [natDegree_pow, mul_comm, h3, roots_minpoly_eq_map_range, map_range_mul_of_periodic]
  intro i
  simp only [pow_add, pow_mul, hper]
end GlobalTheory.CuspGL
