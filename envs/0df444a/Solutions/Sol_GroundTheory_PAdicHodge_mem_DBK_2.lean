-- Prove2me | solution 2 for GroundTheory.PAdicHodge.mem_DBK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:50.615216+00:00
-- url     : https://prove2.me/submissions/da2f0f4f-32b3-4b4e-95c3-5002ce898ee5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B ρ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x : B ⊗[F] V} : x ∈ DBK G F K B ρ ↔ ∀ g : G, baseChangeRep B ρ g x = x :=
  Iff.rfl
end GroundTheory.PAdicHodge
