-- Prove2me | solution 1 for GroundTheory.ProfCoh.isIntertwiningMap_torsNMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:42.108498+00:00
-- url     : https://prove2.me/submissions/937acf61-0a1b-4ddf-8a7e-917d82307dbe

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake

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
variable {Γ : Type*} [Group Γ] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (n : ℕ)
namespace GroundTheory.ProfCoh
theorem _root_.solution {f : A →+ B} (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) :
    (torsNRep Γ A n).IsIntertwiningMap (torsNRep Γ B n) (torsNMap n f) :=
  ⟨fun γ x => Subtype.ext (hfγ γ x)⟩
end GroundTheory.ProfCoh
