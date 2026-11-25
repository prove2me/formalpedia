-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isOpen_setOf_le_cellRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:07.196989+00:00
-- url     : https://prove2.me/submissions/dcc55b8a-b14e-439f-97da-b66f81e2986f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_setOf_le_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (a b k : ℕ) :
    IsOpen {x : GL (Fin n) F | k ≤ cellRank β γ x a b} :=
  (isOpen_setOf_le_rank k).preimage (Units.continuous_val.matrix_submatrix _ _)
end GroundTheory.Automorphic.Parabolic
