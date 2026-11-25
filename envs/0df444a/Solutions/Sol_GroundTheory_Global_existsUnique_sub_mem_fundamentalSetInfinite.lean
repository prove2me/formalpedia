-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_sub_mem_fundamentalSetInfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:45.740211+00:00
-- url     : https://prove2.me/submissions/e73edd26-49f2-4fab-9c43-89ddb18f0fe7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_algebraMap
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_sub

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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
variable [NumberField K]
open scoped Classical
namespace GroundTheory.Global
theorem _root_.solution (x : K∞) :
    ∃! z : 𝓞 K, x - algebraMap (𝓞 K) K∞ z ∈ fundamentalSetInfinite K := by
  set b := mixedEmbedding.latticeBasis K
  have hmem : ∀ z : 𝓞 K, mixedEmbedding K (z : K) ∈ Submodule.span ℤ (Set.range b) := by
    intro z
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨z, rfl⟩
  have himg : ∀ z : 𝓞 K, homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) =
      homeomorphMixedSpace K x - mixedEmbedding K (z : K) := by
    intro z
    rw [homeomorphMixedSpace_sub, IsScalarTower.algebraMap_apply (𝓞 K) K K∞,
      homeomorphMixedSpace_algebraMap]
  have hinj : Function.Injective fun z : 𝓞 K => mixedEmbedding K (z : K) :=
    (mixedEmbedding K).injective.comp RingOfIntegers.coe_injective
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 K, mixedEmbedding K (z : K) =
      (ZSpan.floor b (homeomorphMixedSpace K x) : mixedEmbedding.mixedSpace K) := by
    have := (ZSpan.floor b (homeomorphMixedSpace K x)).2
    rw [mixedEmbedding.mem_span_latticeBasis] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩
  refine ⟨z, ?_, fun z' hz' => ?_⟩
  · change homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) ∈ ZSpan.fundamentalDomain b
    rw [himg, hz]
    exact ZSpan.fract_mem_fundamentalDomain b _
  · replace hz' : homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z') ∈
        ZSpan.fundamentalDomain b := hz'
    rw [himg] at hz'
    have h1 : homeomorphMixedSpace K x - mixedEmbedding K (z : K) ∈ ZSpan.fundamentalDomain b := by
      rw [hz]
      exact ZSpan.fract_mem_fundamentalDomain b _
    rw [← ZSpan.fract_eq_self] at h1 hz'
    have heq : ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) =
        ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) := by
      rw [ZSpan.fract_eq_fract]
      have : -(homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) +
          (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) =
          mixedEmbedding K (z' : K) - mixedEmbedding K (z : K) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hmem z') (hmem z)
    rw [hz', h1] at heq
    exact hinj (sub_right_injective heq)
end GroundTheory.Global
