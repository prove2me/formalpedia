-- Prove2me | solution 1 for MurtySimon.sum_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:00.100155+00:00
-- url     : https://prove2.me/submissions/0f80ab19-a4f7-44f2-a26d-80b2eefc1fd7

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
namespace MurtySimon
theorem _root_.solution : ∑ p ∈ exits G M, wt M p ≤ 2 * #(Nc G) := by
  have hmaps : ∀ p ∈ exits G M, s(p.1, p.2) ∈ Nc G := by
    intro p hp
    obtain ⟨h1, h2, -, -⟩ := (mem_filter.1 hp).2
    exact mem_filter.2 ⟨mem_univ _, h1, h2⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ f ∈ Nc G, ∑ p ∈ (exits G M).filter (fun p => s(p.1, p.2) = f), wt M p
      ≤ ∑ _f ∈ Nc G, 2 := by
        apply sum_le_sum
        intro f hf
        induction f using Sym2.ind with
        | h x y =>
          have hxy : x ≠ y := by
            have := (mem_filter.1 hf).2.1
            rw [mem_edgeSet, compl_adj] at this
            exact this.1
          have hsub : (exits G M).filter (fun p => s(p.1, p.2) = s(x, y)) ⊆
              ({(x, y), (y, x)} : Finset (V × V)).filter (· ∈ exits G M) := by
            intro p hp
            obtain ⟨hpX, hpf⟩ := mem_filter.1 hp
            refine mem_filter.2 ⟨?_, hpX⟩
            rcases Sym2.eq_iff.1 hpf with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp [Prod.ext_iff, h1, h2]
            · simp [Prod.ext_iff, h1, h2]
          refine (sum_le_sum_of_subset hsub).trans ?_
          have hne : (x, y) ≠ (y, x) := fun h => hxy (Prod.ext_iff.1 h).1
          rw [sum_filter, sum_pair hne]
          simp only [exits, mem_filter, mem_univ, true_and, IsExit, wt]
          by_cases hx : Covered M x <;> by_cases hy : Covered M y <;> simp [hx, hy] <;>
            split_ifs <;> omega
    _ = 2 * #(Nc G) := by rw [sum_const, smul_eq_mul, mul_comm]
end MurtySimon
