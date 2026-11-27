-- Prove2me | solution 1 for MohP3.Wt.exists_yOrd_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:20:58.183643+00:00
-- url     : https://prove2.me/submissions/e3b5fe14-9499-48b8-a7c4-feef507bae8d

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
theorem _root_.solution (g : ℕ → PowerSeries k) (s₀ : ℕ)
    (hg : ∀ s, YOrd (g s) (s - s₀)) :
    ∃ G : PowerSeries k, ∀ M, YOrd (G - ∑ s ∈ Finset.range M, g s) (M - s₀) := by
  refine ⟨PowerSeries.mk fun m => ∑ s ∈ Finset.range (8 * m + s₀ + 1), PowerSeries.coeff m (g s),
    ?_⟩
  intro M m hm
  have hMle : 8 * m + s₀ + 1 ≤ M := by omega
  have hzero : ∀ s ∈ Finset.range M, s ∉ Finset.range (8 * m + s₀ + 1) →
      PowerSeries.coeff m (g s) = 0 := by
    intro s _ hs
    rw [Finset.mem_range] at hs
    exact hg s m (by omega)
  have hsub : Finset.range (8 * m + s₀ + 1) ⊆ Finset.range M := by
    intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
  simp only [map_sub, PowerSeries.coeff_mk, map_sum]
  rw [Finset.sum_subset hsub hzero, sub_self]
end MohP3.Wt
