-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.smul_mem_fixedModule_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:45.189675+00:00
-- url     : https://prove2.me/submissions/fdd197e9-ee16-4a29-8a33-9ce5d47fd5f5

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
variable (K L : Subgroup G)
variable {A K L}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hLK : L ≤ K) [hN : (L.subgroupOf K).Normal] {g : G}
    (hg : g ∈ K) {a : A} (ha : a ∈ fixedModule A L) : g • a ∈ fixedModule A L := by
  intro h hh
  have hc : g⁻¹ * h * g ∈ L := by
    have := hN.conj_mem ⟨h, hLK hh⟩ (by simpa [Subgroup.mem_subgroupOf] using hh) ⟨g, hg⟩⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  calc h • g • a = g • (g⁻¹ * h * g) • a := by simp [smul_smul, mul_assoc]
    _ = g • a := by rw [ha _ hc]
end GroundTheory.LocalField.Abstract
