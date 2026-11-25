-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_sub_mem_fundamentalSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:46.536801+00:00
-- url     : https://prove2.me/submissions/6cd5c8d1-cd88-4bbd-bd97-86c989dc85de

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Theorems.Thm_GroundTheory_Global_exists_eq_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_algebraMap_integers_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_existsUnique_sub_mem_fundamentalSetInfinite
import Theorems.Thm_GroundTheory_Global_exists_sub_mem_integralFiniteAdeles


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
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (x : 𝔸[K]) :
    ∃! k : K, x - algebraMap K 𝔸[K] k ∈ fundamentalSet K := by
  obtain ⟨k₁, hk₁⟩ := exists_sub_mem_integralFiniteAdeles x.2
  obtain ⟨z, hz, -⟩ := existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)
  refine ⟨k₁ + z, ⟨?_, ?_⟩, fun k hk => ?_⟩
  · change x.1 - algebraMap K K∞ (k₁ + z) ∈ _
    rw [map_add, ← sub_sub, ← IsScalarTower.algebraMap_apply]
    exact hz
  · change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) (k₁ + z) ∈ _
    rw [map_add, ← sub_sub]
    exact Subring.sub_mem _ hk₁ (algebraMap_integers_mem_integralFiniteAdeles K z)
  · obtain ⟨hkinf, hkf⟩ := hk
    change x.1 - algebraMap K K∞ k ∈ fundamentalSetInfinite K at hkinf
    change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ integralFiniteAdeles (𝓞 K) K at hkf

    have hdiff : algebraMap K (FiniteAdeleRing (𝓞 K) K) (k - (k₁ + z)) ∈
        integralFiniteAdeles (𝓞 K) K := by
      have h2 := Subring.sub_mem _ (Subring.sub_mem _ hk₁ hkf)
        (algebraMap_integers_mem_integralFiniteAdeles K z)
      convert h2 using 1
      simp only [map_sub, map_add]
      abel
    obtain ⟨u, hu⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K _ hdiff
    have h1 : z + u = z := by
      refine (existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)).unique
        ?_ hz
      convert hkinf using 1
      have hu' : algebraMap (𝓞 K) K u = k - (k₁ + algebraMap (𝓞 K) K z) := hu
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K K∞, map_add, hu']
      simp only [map_sub, map_add]
      abel
    have hu0 : u = 0 := by simpa using h1
    rw [hu0] at hu
    have : k - (k₁ + z) = 0 := by rw [← hu]; simp
    exact sub_eq_zero.mp this
end GroundTheory.Global
