-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:31.927046+00:00
-- url     : https://prove2.me/submissions/58d15c83-ee1f-4470-a0c7-09038ae035e0

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
theorem _root_.solution {b : ℕ} (hb : Finset.univ.sup γ ≤ b) (g : GL (Fin n) F) (a : ℕ) :
    cellRank β γ g a b = cellRank β γ g a (Finset.univ.sup γ) := by
  classical
  have key : ∀ c, Finset.univ.sup γ ≤ c → cellRank β γ g a c =
      ((g : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
        id).rank := by
    intro c hc
    have hall : ∀ j, γ j ≤ c := fun j => (Finset.le_sup (Finset.mem_univ j)).trans hc
    unfold cellRank
    rw [← Matrix.rank_submatrix _ (Equiv.refl _) (Equiv.subtypeUnivEquiv hall)]
    rfl
  rw [key b hb, key _ le_rfl]
end GroundTheory.Automorphic.Parabolic
