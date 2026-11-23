-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:31.227584+00:00
-- url     : https://prove2.me/submissions/ef05e7a4-0a34-4f0a-9306-675cb5704eca

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
namespace GroundTheory.Automorphic.ContragredientTranspose
namespace ContCoeff
theorem _root_.solution {P Q : α → F[X]} (hP : ContCoeff P) (hQ : ContCoeff Q) :
    ContCoeff fun a => P a * Q a := fun k => by
  simp only [coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hP x.1).mul (hQ x.2)
end ContCoeff
end GroundTheory.Automorphic.ContragredientTranspose
