-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.mem_orthIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:16.153588+00:00
-- url     : https://prove2.me/submissions/698d3b89-7209-42dc-800b-494ac634a4b0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}
namespace GroundTheory.Automorphic.PeterssonComplement
theorem _root_.solution {U : Submodule ℂ V} {v : V} :
    v ∈ orthIn ι U ↔ ∀ u ∈ U, inner ℂ (ι u) (ι v) = 0 := Iff.rfl
end GroundTheory.Automorphic.PeterssonComplement
