-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRank_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:58.00281+00:00
-- url     : https://prove2.me/submissions/08d9648c-a350-4690-9acb-cdc02664af16

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells

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
theorem _root_.solution {a : ℕ} (ha : Finset.univ.sup β < a) (g : GL (Fin n) F) (b : ℕ) :
    cellRank β γ g a b = 0 := by
  unfold cellRank
  have hcard : Fintype.card {i : Fin n // a ≤ β i} = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun i => absurd (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i.1)) ha) (not_lt.2 i.2)⟩
  exact Nat.le_zero.1 (hcard ▸ Matrix.rank_le_card_height _)
end GroundTheory.Automorphic.Parabolic
