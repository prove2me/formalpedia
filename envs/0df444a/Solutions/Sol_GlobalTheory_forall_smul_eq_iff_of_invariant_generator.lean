-- Prove2me | solution 1 for GlobalTheory.forall_smul_eq_iff_of_invariant_generator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:41.648683+00:00
-- url     : https://prove2.me/submissions/2849d4e5-dae9-44af-9cd8-75f3f3635110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
variable {A M}
namespace GlobalTheory
theorem _root_.solution {n : M}
    (hn : Function.Bijective (LinearMap.toSpanSingleton A M n)) (hn' : ∀ g : G, g • n = n)
    (y : M) : (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • n := by
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := hn.2 y
    refine ⟨a, fun g ↦ hn.1 ?_, rfl⟩
    simpa [smul_distrib_smul, hn'] using hy g
  · rintro ⟨a, ha, rfl⟩ g
    rw [smul_distrib_smul, ha g, hn']
end GlobalTheory
