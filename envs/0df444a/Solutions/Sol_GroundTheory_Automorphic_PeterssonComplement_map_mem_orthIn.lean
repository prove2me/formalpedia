-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.map_mem_orthIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:14.450802+00:00
-- url     : https://prove2.me/submissions/2a7bb098-c554-4351-b303-9b38dc7fd451

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
theorem _root_.solution {U : Submodule ℂ V} {A A' : V → V}
    (hA : ∀ x y, inner ℂ (ι (A' x)) (ι y) = inner ℂ (ι x) (ι (A y))) (hU : ∀ u ∈ U, A' u ∈ U)
    {v : V} (hv : v ∈ orthIn ι U) : A v ∈ orthIn ι U := fun u hu => by
  rw [← hA]
  exact hv _ (hU u hu)
end GroundTheory.Automorphic.PeterssonComplement
