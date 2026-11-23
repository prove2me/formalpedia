-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ellQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:51.549249+00:00
-- url     : https://prove2.me/submissions/3e7a4333-d88c-4c0d-9bb5-2412ebcfc089

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
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (f : F[X]) : ellQ q hq (Submodule.Quotient.mk f) = lcoeffMod q f := rfl
end GroundTheory.Automorphic.ContragredientTranspose
