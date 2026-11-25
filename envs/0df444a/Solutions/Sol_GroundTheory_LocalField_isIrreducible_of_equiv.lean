-- Prove2me | solution 1 for GroundTheory.LocalField.isIrreducible_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:33.636691+00:00
-- url     : https://prove2.me/submissions/329da4d5-0a29-4f33-93f0-26477186a244

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.LocalField
theorem _root_.solution {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) [ρ.IsIrreducible] : σ.IsIrreducible :=
  (subrepOrderIso φ).isSimpleOrder_iff.mp inferInstance
end GroundTheory.LocalField
