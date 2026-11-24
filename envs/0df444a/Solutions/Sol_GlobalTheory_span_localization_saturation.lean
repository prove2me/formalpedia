-- Prove2me | solution 1 for GlobalTheory.span_localization_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:46.059988+00:00
-- url     : https://prove2.me/submissions/3b3fc69b-253e-46e6-ad04-7e6c9e05d029

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S] {V : Type*} [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]
include p
namespace GlobalTheory
theorem _root_.solution (hp : p ≤ R⁰) (N : Submodule R V) :
    Submodule.span S (saturation N : Set V) = saturation (Submodule.span S (N : Set V)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
    refine mem_saturation_iff'.2
      ⟨algebraMap R S a, IsLocalization.nonZeroDivisors_le_comap (M := p) (S := S) ha, ?_⟩
    rw [algebraMap_smul]
    exact Submodule.subset_span hax
  · intro y hy
    obtain ⟨b, hb, hby⟩ := mem_saturation_iff'.1 hy
    obtain ⟨c, hc, hcb⟩ := (mem_span_localization_iff S p N _).1 hby
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective p b
    have hr : r ∈ R⁰ := by
      have h1 : algebraMap R S r ∈ S⁰ := by
        rw [← IsLocalization.mk'_spec S r t]
        exact mul_mem hb (IsLocalization.map_units S t).mem_nonZeroDivisors
      exact mem_nonZeroDivisors_of_injective (IsLocalization.injective S hp) h1
    have e : (t : R) • c • (IsLocalization.mk' S r t • y) = (c * r) • y := by
      rw [smul_comm c (IsLocalization.mk' S r t) y, ← algebraMap_smul S (t : R),
        smul_smul (algebraMap R S t), IsLocalization.mk'_spec', algebraMap_smul, smul_smul,
        mul_comm]
    refine Submodule.subset_span (mem_saturation_iff'.2 ⟨c * r, mul_mem (hp hc) hr, ?_⟩)
    rw [← e]
    exact N.smul_mem _ hcb
end GlobalTheory
