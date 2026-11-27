-- Prove2me | solution 1 for GroundTheory.Automorphic.elementarySubgroup_le_ker_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:04.538085+00:00
-- url     : https://prove2.me/submissions/ca403cd1-5dce-4873-8525-c0a407234567

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}
namespace GroundTheory.Automorphic
theorem _root_.solution :
    elementarySubgroup n R ≤ (Matrix.GeneralLinearGroup.det : GL n R →* Rˣ).ker := by
  rw [elementarySubgroup, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, TransvectionStruct.det]
end GroundTheory.Automorphic
