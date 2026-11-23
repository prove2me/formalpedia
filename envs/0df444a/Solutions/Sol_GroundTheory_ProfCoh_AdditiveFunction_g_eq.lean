-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:44.721556+00:00
-- url     : https://prove2.me/submissions/155b6fee-d40d-44b7-83cf-940168e6b83d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite (ModN A l)]
    [Finite (TorsN A l)] :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) - d.toFun (TorsN A l) (torsNRep Γ A l) := by
  rw [g, dif_pos ⟨‹_›, ‹_›⟩]
end GroundTheory.ProfCoh.AdditiveFunction
