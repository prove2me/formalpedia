-- Prove2me | solution 1 for GroundTheory.LocalField.spanZ_le_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:37.879015+00:00
-- url     : https://prove2.me/submissions/e54f0dfb-36ab-46cd-b432-31c0a019ab9f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan

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
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]
variable (E : Subgroup G → Prop)
variable {E}
namespace GroundTheory.LocalField
theorem _root_.solution (ζ : ℂ) : spanZ E ≤ spanA E ζ := fun g hg ↦
  Submodule.subset_span ⟨1, Subalgebra.one_mem _, g, hg, (one_smul ℂ g).symm⟩
end GroundTheory.LocalField
