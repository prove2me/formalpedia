-- Prove2me | solution 1 for GroundTheory.Global.finite_kerModRange_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:42.436046+00:00
-- url     : https://prove2.me/submissions/ea0884f8-1ca9-451f-9c3f-cf1b357afc41

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic

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
open GroundTheory.GroupCoh
namespace GroundTheory.Global
theorem _root_.solution {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    (f g : A →+ A) {n : ℤ} (hn : n ≠ 0) (h : ∀ x ∈ f.ker, n • x ∈ g.range) :
    Finite (KerModRange f g) := by
  have hfin : Module.Finite ℤ f.ker := by
    have : Module.Finite ℤ (LinearMap.ker f.toIntLinearMap) := inferInstance
    exact Module.Finite.equiv (R := ℤ)
      ((LinearEquiv.refl ℤ (LinearMap.ker f.toIntLinearMap)) : _ ≃ₗ[ℤ] f.ker)
  have hq : Module.Finite ℤ (KerModRange f g) :=
    Module.Finite.of_surjective
      (QuotientAddGroup.mk' (g.range.addSubgroupOf f.ker)).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (g.range.addSubgroupOf f.ker) y
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
  show n • (QuotientAddGroup.mk' _ x : KerModRange f g) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_zsmul]
  exact h x x.2
end GroundTheory.Global
