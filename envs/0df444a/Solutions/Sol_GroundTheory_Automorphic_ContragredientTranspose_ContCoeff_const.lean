-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:36.103045+00:00
-- url     : https://prove2.me/submissions/f1d03b84-c43d-4454-8808-d8b23cfc51ca

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
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {α : Type*} [TopologicalSpace α]
omit [IsTopologicalRing F]
namespace GroundTheory.Automorphic.ContragredientTranspose
namespace ContCoeff
theorem _root_.solution (p : F[X]) : ContCoeff fun _ : α => p := fun _ => continuous_const
end ContCoeff
end GroundTheory.Automorphic.ContragredientTranspose
