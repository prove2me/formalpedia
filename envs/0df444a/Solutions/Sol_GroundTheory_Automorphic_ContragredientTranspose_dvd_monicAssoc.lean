-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.dvd_monicAssoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:46.149812+00:00
-- url     : https://prove2.me/submissions/a996f1ec-f5be-4db0-a121-4fde33dfdf5f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
variable {F : Type*} [Field F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (q : F[X]) : q ∣ monicAssoc q := Dvd.intro _ rfl
end GroundTheory.Automorphic.ContragredientTranspose
