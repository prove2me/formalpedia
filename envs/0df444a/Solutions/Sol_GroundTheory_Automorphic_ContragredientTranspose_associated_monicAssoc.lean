-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.associated_monicAssoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:03.237048+00:00
-- url     : https://prove2.me/submissions/4de7853e-e739-4215-8553-bdd7e0c55fc4

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
theorem _root_.solution {q : F[X]} (hq : q ≠ 0) : Associated q (monicAssoc q) :=
  associated_mul_unit_right _ _ (isUnit_C.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hq)).isUnit)
end GroundTheory.Automorphic.ContragredientTranspose
