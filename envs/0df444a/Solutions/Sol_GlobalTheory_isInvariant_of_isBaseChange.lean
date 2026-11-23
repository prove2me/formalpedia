-- Prove2me | solution 1 for GlobalTheory.isInvariant_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:28.407978+00:00
-- url     : https://prove2.me/submissions/07e4181d-4f2a-4e16-a34d-67d79a50c92a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isBaseChange_fixedSubalgebraMap

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
variable (G : Type*) [Group G]
variable {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
  [Algebra R S] [Algebra R A] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
  [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A'] [SMulCommClass G S A']
namespace GlobalTheory
theorem _root_.solution [Finite G] [Module.Flat R S] [Algebra.IsInvariant R A G]
    (f : A →ₐ[R] A') (hb : IsBaseChange S f.toLinearMap)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) : Algebra.IsInvariant S A' G := by
  refine ⟨fun y hy ↦ ?_⟩
  have key : ∀ z : FixedPoints.subalgebra S A' G, ∃ s, algebraMap S A' s = z := by
    intro z
    induction z using (isBaseChange_fixedSubalgebraMap G f hb hf).inductionOn with
    | zero => exact ⟨0, map_zero _⟩
    | tmul m =>
      obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) (m : A) m.2
      refine ⟨algebraMap R S r, ?_⟩
      change _ = f m
      rw [← hr, f.commutes, ← IsScalarTower.algebraMap_apply]
    | smul s n hn =>
      obtain ⟨t, ht⟩ := hn
      exact ⟨s * t, by rw [map_mul, ht, ← Algebra.smul_def]; rfl⟩
    | add a b ha hb =>
      obtain ⟨t, ht⟩ := ha
      obtain ⟨u, hu⟩ := hb
      exact ⟨t + u, by rw [map_add, ht, hu]; rfl⟩
  exact key ⟨y, hy⟩
end GlobalTheory
