-- Prove2me | solution 1 for MohP3.Wt.exists_wOrd_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:21:13.800936+00:00
-- url     : https://prove2.me/submissions/6de8262f-9cce-4c3f-87a1-0089a9d7b24f

module
public import Mathlib
public import Definitions.Def_MohP3_Order

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (g : ℕ → MvPowerSeries (Fin 3) k) (s₀ : ℕ)
    (hg : ∀ s, WOrd (g s) (s - s₀)) :
    ∃ G : MvPowerSeries (Fin 3) k, ∀ M, WOrd (G - ∑ s ∈ Finset.range M, g s) (M - s₀) := by
  let G : MvPowerSeries (Fin 3) k :=
    fun d => ∑ s ∈ Finset.range (wt d + s₀ + 1), coeff d (g s)
  refine ⟨G, ?_⟩
  intro M d hd
  have hMle : wt d + s₀ + 1 ≤ M := by omega
  have hzero : ∀ s ∈ Finset.range M, s ∉ Finset.range (wt d + s₀ + 1) → coeff d (g s) = 0 := by
    intro s _ hs
    rw [Finset.mem_range] at hs
    exact hg s d (by omega)
  have hco : coeff d G = ∑ s ∈ Finset.range (wt d + s₀ + 1), coeff d (g s) := rfl
  have hsub : Finset.range (wt d + s₀ + 1) ⊆ Finset.range M := by
    intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
  rw [map_sub, hco, map_sum, Finset.sum_subset hsub hzero, sub_self]
end MohP3.Wt
