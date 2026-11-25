-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.lcoeffMod_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:44.701067+00:00
-- url     : https://prove2.me/submissions/f421081c-c881-42c8-9d8b-5faa46370c47

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
theorem _root_.solution (q : F[X]) (c : F) (f : F[X]) :
    lcoeffMod q (C c * f) = c * lcoeffMod q f := by
  simp [lcoeffMod, ← smul_eq_C_mul, smul_modByMonic]
end GroundTheory.Automorphic.ContragredientTranspose
