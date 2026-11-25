-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellHeight_of_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:46:47.208303+00:00
-- url     : https://prove2.me/submissions/7a5a3aa9-a419-4c62-9ab1-40988de61541

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_of_mem_doubleCoset
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
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
omit [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {g x : GL (Fin n) F}
    (hx : x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) :
    cellHeight β γ x = cellHeight β γ g := by
  unfold cellHeight
  simp only [cellRank_of_mem_doubleCoset hx]
end GroundTheory.Automorphic.Parabolic
