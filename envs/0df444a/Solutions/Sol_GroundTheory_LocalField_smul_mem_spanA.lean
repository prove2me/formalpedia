-- Prove2me | solution 1 for GroundTheory.LocalField.smul_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:58:23.593547+00:00
-- url     : https://prove2.me/submissions/db051168-f874-44b5-b4eb-50313f4b0252

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
theorem _root_.solution {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {g : G → ℂ}
    (hg : g ∈ spanZ E) : a • g ∈ spanA E ζ :=
  Submodule.subset_span ⟨a, ha, g, hg, rfl⟩
end GroundTheory.LocalField
