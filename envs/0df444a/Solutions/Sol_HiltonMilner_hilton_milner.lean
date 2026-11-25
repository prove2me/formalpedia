-- Prove2me | solution 1 for HiltonMilner.hilton_milner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:39.613562+00:00
-- url     : https://prove2.me/submissions/98312578-087d-4c1a-97a3-987aa5ebff39

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
public import Theorems.Thm_HiltonMilner_hm_bound


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) (hs : (𝒜 : Set (Finset (Fin n))).Sized k)
    (hnt : ∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) :
    #𝒜 ≤ (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 := by
  set f : Finset (Fin n) ↪ Finset ℕ := ⟨fun A => A.map Fin.valEmbedding, map_injective _⟩
  have := hm_bound n k hk hkn.le (range n) (card_range n) (𝒜.map f) ?_ ?_ ?_
  · rwa [card_map] at this
  · intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := mem_map.1 hA
    refine mem_powersetCard.2 ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨y, -, rfl⟩ := mem_map.1 hx
      exact mem_range.2 y.isLt
    · change #(A₀.map Fin.valEmbedding) = k
      rw [card_map]; exact hs hA₀
  · intro A hA B hB
    obtain ⟨A₀, hA₀, rfl⟩ := mem_map.1 hA
    obtain ⟨B₀, hB₀, rfl⟩ := mem_map.1 hB
    obtain ⟨w, hw⟩ := not_disjoint_iff_nonempty_inter.1 (h𝒜 hA₀ hB₀)
    exact ⟨w.val, by
      rw [mem_inter]
      exact ⟨mem_map_of_mem _ (mem_inter.1 hw).1, mem_map_of_mem _ (mem_inter.1 hw).2⟩⟩
  · intro x hx
    obtain ⟨A, hA, hxA⟩ := hnt ⟨x, mem_range.1 hx⟩
    refine ⟨f A, mem_map_of_mem _ hA, fun h => hxA ?_⟩
    obtain ⟨y, hy, hyx⟩ := mem_map.1 h
    have : y = ⟨x, mem_range.1 hx⟩ := Fin.ext hyx
    exact this ▸ hy
end HiltonMilner
