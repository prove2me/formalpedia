-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.apply_aeval_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:45.971616+00:00
-- url     : https://prove2.me/submissions/f6cd9899-fe3f-4819-8e31-e808e8532375

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
theorem _root_.solution (T : Module.End ℂ V) (q : ℂ[X]) (z : V) : T (aeval T q z) = aeval T q (T z) := by
  have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
  rw [aeval_X] at h
  exact congrArg (fun L : Module.End ℂ V => L z) h.eq
end GroundTheory.Automorphic.PeterssonComplement
