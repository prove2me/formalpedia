-- Prove2me | solution 1 for GlobalTheory.exists_inner_dual_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:22.230831+00:00
-- url     : https://prove2.me/submissions/6818ea59-effa-4dde-bc27-01e7b9473218

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsBasisSpanEqOfDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {N : ℕ} (b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ d : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), ∀ j y, inner ℝ (d j) y = b.repr y j := by
  let w : Fin N → EuclideanSpace ℝ (Fin N) := fun j =>
    (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap (b.coord j))
  have hw : ∀ j y, inner ℝ (w j) y = b.repr y j := fun j y => by
    simp [w, InnerProductSpace.toDual_symm_apply]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun x => inner ℝ x (b i)) hg
    simpa [sum_inner, real_inner_smul_left, hw, Finsupp.single_apply] using this
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp), fun j y => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', hw]
end GlobalTheory
