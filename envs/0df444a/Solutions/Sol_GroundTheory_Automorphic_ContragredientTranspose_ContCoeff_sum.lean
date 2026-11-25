-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:01.531805+00:00
-- url     : https://prove2.me/submissions/f0a084aa-360d-444e-8119-a56dc3b9c726

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {P : ι → α → F[X]}
    (hP : ∀ i ∈ s, ContCoeff (P i)) : ContCoeff fun a => ∑ i ∈ s, P i a := fun k => by
  simp only [finsetSum_coeff]
  exact continuous_finsetSum _ fun i hi => hP i hi k
end ContCoeff
end GroundTheory.Automorphic.ContragredientTranspose
