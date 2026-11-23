-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.smul_mem_fixedModule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:47.321237+00:00
-- url     : https://prove2.me/submissions/093d1b8f-ff80-4325-bbc4-f43ab9315eb5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable {A}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {H : Subgroup G} {a : A} (ha : a ∈ fixedModule A H) (g : G) :
    g • a ∈ fixedModule A (H.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨h, hh, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← mul_smul]
  rw [show g * h * g⁻¹ * g = g * h by group, mul_smul, ha h hh]
end GroundTheory.LocalField.Abstract
