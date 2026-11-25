-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:45.120289+00:00
-- url     : https://prove2.me/submissions/8852c328-a7a6-46b8-a2f7-125de0f4061c

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
theorem _root_.solution {T : Module.End ℂ V} {Z : Submodule ℂ V} (hZ : ∀ z ∈ Z, T z ∈ Z) (q : ℂ[X]) :
    ∀ z ∈ Z, aeval T q z ∈ Z := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro z hz
    rw [aeval_C, Module.algebraMap_end_apply]
    exact Z.smul_mem a hz
  | add p q hp hq =>
    intro z hz
    rw [map_add, LinearMap.add_apply]
    exact Z.add_mem (hp z hz) (hq z hz)
  | monomial k a ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (hZ z hz)
end GroundTheory.Automorphic.PeterssonComplement
