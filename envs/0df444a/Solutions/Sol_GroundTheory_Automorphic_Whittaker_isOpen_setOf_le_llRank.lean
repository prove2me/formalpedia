-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isOpen_setOf_le_llRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:52.665611+00:00
-- url     : https://prove2.me/submissions/3f47a400-985f-4b22-8386-8eca23421d90

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_le_rank_iff_exists_det_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (i j : Fin n) (k : ℕ) :
    IsOpen {g : GL (Fin n) F | k ≤ llRank i j g} := by
  have e : {g : GL (Fin n) F | k ≤ llRank i j g} =
      ⋃ (A : Matrix (Fin k) (Fin n) F) (B : Matrix (Fin n) (Fin k) F),
        {g | (A * (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j) * B).det ≠ 0} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, llRank]
    exact le_rank_iff_exists_det_ne_zero _ k
  rw [e]
  refine isOpen_iUnion fun A => isOpen_iUnion fun B => ?_
  have hc : Continuous fun g : GL (Fin n) F =>
      (A * (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j) * B).det :=
    ((continuous_const.matrix_mul ((continuous_const.matrix_mul Units.continuous_val).matrix_mul
      continuous_const)).matrix_mul continuous_const).matrix_det
  exact isOpen_compl_singleton.preimage hc
end GroundTheory.Automorphic.Whittaker
