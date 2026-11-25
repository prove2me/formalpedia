-- Prove2me | solution 1 for GroundTheory.Global.continuous_equiv_symm_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:12.526665+00:00
-- url     : https://prove2.me/submissions/5d436455-8710-49ce-b46f-8bf5d702f671

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ Y) (h : X ≃ₜ Y) (he : ∀ x, e x = h x) : Continuous e.symm :=
  h.symm.continuous.congr fun y ↦ e.injective (by rw [e.apply_symm_apply, he, h.apply_symm_apply])
end GroundTheory.Global
