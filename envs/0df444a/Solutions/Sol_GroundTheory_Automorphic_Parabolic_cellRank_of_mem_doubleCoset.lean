-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRank_of_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:56.16117+00:00
-- url     : https://prove2.me/submissions/2573f4b1-ab87-4145-86b4-ed4fc6b56c79

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_mul_mul

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {g x : GL (Fin n) F}
    (hx : x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) (a b : ℕ) :
    cellRank β γ x a b = cellRank β γ g a b := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_doubleCoset.1 hx
  exact cellRank_mul_mul hp hq g a b
end GroundTheory.Automorphic.Parabolic
