-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_boxSubgroup_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:49.741003+00:00
-- url     : https://prove2.me/submissions/cfc94abb-4692-4982-9ee1-6133e6c3edf5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Set Topology
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {K : ∀ v, Subgroup (G v)}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution [∀ v, IsTopologicalGroup (G v)]
    [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
    [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] (hKc : ∀ v, IsCompact (K v : Set (G v)))
    {U : Set (Πʳ v, [G v, K v])} (hU : U ∈ 𝓝 1) :
    ∃ K' : ∀ v, Subgroup (G v), (∀ v, IsCompact (K' v : Set (G v))) ∧
      (∀ v, IsOpen (K' v : Set (G v))) ∧ (∀ v, K' v ≤ K v) ∧ (∀ᶠ v in cofinite, K' v = K v) ∧
        (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) ⊆ U := by
  classical
  set x₁ : ∀ v, ((K v : Set (G v)) : Type _) := fun v => ⟨1, (K v).one_mem⟩
  have h1 : RestrictedProduct.structureMap G (fun v => (K v : Set (G v))) cofinite x₁ = 1 :=
    Subtype.ext rfl
  rw [← h1, RestrictedProduct.nhds_eq_map_structureMap hKo.out, Filter.mem_map, nhds_pi,
    Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hIt⟩ := hU
  have hloc : ∀ v, ∃ L : Subgroup (G v), IsCompact (L : Set (G v)) ∧ IsOpen (L : Set (G v)) ∧
      L ≤ K v ∧ (v ∈ I → ∀ g ∈ L, ∀ hg : g ∈ K v, (⟨g, hg⟩ : (K v : Set (G v))) ∈ t v) := by
    intro v
    by_cases hv : v ∈ I
    · have hnhds : ((↑) : ((K v : Set (G v)) : Type _) → G v) '' t v ∈ 𝓝 (1 : G v) :=
        (hKo.out v).isOpenEmbedding_subtypeVal.image_mem_nhds.2 (ht v)
      obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset hnhds
      refine ⟨L, hLc, L.isOpen, fun g hg => ?_, fun _ g hg hgK => ?_⟩
      · obtain ⟨y, _, rfl⟩ := hLU hg
        exact y.2
      · obtain ⟨y, hy, hyg⟩ := hLU hg
        have : y = ⟨g, hgK⟩ := Subtype.ext hyg
        rw [← this]
        exact hy
    · exact ⟨K v, hKc v, hKo.out v, le_rfl, fun h => absurd h hv⟩
  choose L hLc hLo hLK hLt using hloc
  set K' : ∀ v, Subgroup (G v) := fun v => if v ∈ I then L v else K v
  refine ⟨K', fun v => ?_, fun v => ?_, fun v => ?_, ?_, ?_⟩
  · by_cases hv : v ∈ I <;> simp [K', hv, hLc v, hKc v]
  · by_cases hv : v ∈ I <;> simp [K', hv, hLo v, hKo.out v]
  · by_cases hv : v ∈ I <;> simp [K', hv, hLK v]
  · exact Filter.eventually_cofinite.2 (hI.subset fun v hv => by
      by_contra hvI
      exact hv (by simp [K', hvI]))
  · intro g hg
    have hgK : ∀ v, g v ∈ K v := fun v => by
      by_cases hv : v ∈ I
      · have := hg v
        simp only [K', hv, if_true] at this
        exact hLK v this
      · have := hg v
        simpa [K', hv] using this
    have hx : RestrictedProduct.structureMap G (fun v => (K v : Set (G v))) cofinite
        (fun v => ⟨g v, hgK v⟩) = g := Subtype.ext rfl
    rw [← hx]
    refine hIt fun v hv => ?_
    have := hg v
    simp only [K', hv, if_true] at this
    exact hLt v hv (g v) this (hgK v)
end GroundTheory.Automorphic.RestrictedTensor
