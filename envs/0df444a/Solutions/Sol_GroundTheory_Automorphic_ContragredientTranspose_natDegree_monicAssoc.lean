-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.natDegree_monicAssoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:45.553381+00:00
-- url     : https://prove2.me/submissions/ae717ec7-9d97-4c96-b9ff-a60b390a8816

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
theorem _root_.solution {q : F[X]} (hq : q ≠ 0) : (monicAssoc q).natDegree = q.natDegree :=
  natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hq))
end GroundTheory.Automorphic.ContragredientTranspose
