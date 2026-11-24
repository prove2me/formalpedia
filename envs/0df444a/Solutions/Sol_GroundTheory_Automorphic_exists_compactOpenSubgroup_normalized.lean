-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_compactOpenSubgroup_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:16.632701+00:00
-- url     : https://prove2.me/submissions/71bc6094-7969-4f4e-97f6-7393eae0bf17

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
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
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : OpenSubgroup G, IsCompact (N : Set G) ∧ (N : Set G) ⊆ U ∧
      ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
  obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset hU

  have hopen : IsOpen ((fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G)) :=
    L.isOpen.preimage (by fun_prop)
  have hsub : (K : Set G) ×ˢ ({1} : Set G) ⊆
      (fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G) := by
    rintro ⟨k, x⟩ ⟨-, hx⟩
    simp only [mem_singleton_iff] at hx
    simp [hx]
  obtain ⟨u, v, -, hv, hKu, h1v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hopen hsub

  let N₀ : Subgroup G :=
    { carrier := {x | ∀ k ∈ K, k * x * k⁻¹ ∈ L}
      one_mem' := fun k _ => by simp
      mul_mem' := fun {a b} ha hb k hk => by
        have := mul_mem (ha k hk) (hb k hk)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha k hk => by
        have := inv_mem (ha k hk)
        simpa [mul_assoc] using this }
  have hvN : v ⊆ (N₀ : Set G) := fun x hx k hk =>
    huv (show (k, x) ∈ u ×ˢ v from ⟨hKu hk, hx⟩)
  have hN₀n : (N₀ : Set G) ∈ 𝓝 (1 : G) := mem_of_superset (hv.mem_nhds (h1v rfl)) hvN
  have hN₀L : (N₀ : Set G) ⊆ L := fun x hx => by simpa using hx 1 K.one_mem
  let N : OpenSubgroup G := ⟨N₀, N₀.isOpen_of_mem_nhds hN₀n⟩
  refine ⟨N, hLc.of_isClosed_subset N.isClosed hN₀L, hN₀L.trans hLU, fun k hk n hn j hj => ?_⟩
  have := hn (j * k) (mul_mem hj hk)
  simpa [mul_assoc] using this
end GroundTheory.Automorphic
