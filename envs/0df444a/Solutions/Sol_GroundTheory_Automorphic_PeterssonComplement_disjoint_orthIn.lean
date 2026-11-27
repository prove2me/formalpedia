-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.disjoint_orthIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:06.009798+00:00
-- url     : https://prove2.me/submissions/c4a009c4-a1af-40a2-a96a-0eef420660c8

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
theorem _root_.solution (hι : Function.Injective ι) (U : Submodule ℂ V) : Disjoint U (orthIn ι U) := by
  rw [Submodule.disjoint_def]
  intro v hvU hvO
  have h := hvO v hvU
  rw [inner_self_eq_zero] at h
  exact hι (h.trans (map_zero ι).symm)
end GroundTheory.Automorphic.PeterssonComplement
