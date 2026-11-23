-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.mk_mul_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:12.554851+00:00
-- url     : https://prove2.me/submissions/c815c73e-77fb-4d91-8361-b03e3f0f2dec

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
variable {q : F[X]} (hq : q ≠ 0)
omit hq
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (f g : F[X]) :
    (Submodule.Quotient.mk f : F[X] ⧸ F[X] ∙ q) * Submodule.Quotient.mk g =
      Submodule.Quotient.mk (f * g) := rfl
end GroundTheory.Automorphic.ContragredientTranspose
