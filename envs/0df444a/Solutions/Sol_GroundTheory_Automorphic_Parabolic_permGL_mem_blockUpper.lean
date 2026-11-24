-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.permGL_mem_blockUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:14.874792+00:00
-- url     : https://prove2.me/submissions/9b42ba70-9ba1-4b33-87d8-0c1d52774f88

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply


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
variable {β γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {u : Equiv.Perm (Fin n)} (hu : ∀ x, β (u x) = β x) :
    permGL F u ∈ blockUpper F n β := by
  intro i j hij
  show ((permGL F u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0
  rw [permGL_apply, if_neg]
  rintro rfl
  rw [hu] at hij
  exact lt_irrefl _ hij
end GroundTheory.Automorphic.Parabolic
