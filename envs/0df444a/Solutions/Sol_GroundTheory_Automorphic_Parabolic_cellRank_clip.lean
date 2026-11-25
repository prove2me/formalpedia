-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRank_clip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:25.367418+00:00
-- url     : https://prove2.me/submissions/4d7dce2c-8791-4756-adf3-fe7b1c973d7d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_eq_zero_of_lt
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_eq_of_le

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
theorem _root_.solution (g : GL (Fin n) F) (a b : ℕ) :
    cellRank β γ g a b =
      cellRank β γ g (min a (Finset.univ.sup β + 1)) (min b (Finset.univ.sup γ)) := by
  rcases le_or_gt a (Finset.univ.sup β + 1) with ha | ha
  · rw [min_eq_left ha]
    rcases le_or_gt b (Finset.univ.sup γ) with hb | hb
    · rw [min_eq_left hb]
    · rw [min_eq_right hb.le, cellRank_eq_of_le hb.le]
  · rw [min_eq_right ha.le, cellRank_eq_zero_of_lt (by omega), cellRank_eq_zero_of_lt (by omega)]
end GroundTheory.Automorphic.Parabolic
