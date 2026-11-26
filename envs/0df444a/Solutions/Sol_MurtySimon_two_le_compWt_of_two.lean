-- Prove2me | solution 1 for MurtySimon.two_le_compWt_of_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:34.258993+00:00
-- url     : https://prove2.me/submissions/10d371a1-002c-45bc-8c43-79e08fcda3a5

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_one_le_wt
public import Theorems.Thm_MurtySimon_IsMid_symm


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
theorem _root_.solution {C : (aux G M).ConnectedComponent} {p q : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) (hq : q ∈ exits G M) (hqC : compOf G M q = C)
    (hpq : p ≠ q) : 2 ≤ compWt C := by
  have hsub : ({p, q} : Finset (V × V)) ⊆ (exits G M).filter (fun p => compOf G M p = C) := by
    intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · exact mem_filter.2 ⟨hp, hpC⟩
    · rw [mem_singleton.1 hr]; exact mem_filter.2 ⟨hq, hqC⟩
  calc 2 ≤ wt M p + wt M q := by have := one_le_wt (M := M) p; have := one_le_wt (M := M) q; omega
    _ = ∑ r ∈ ({p, q} : Finset (V × V)), wt M r := (sum_pair hpq).symm
    _ ≤ compWt C := sum_le_sum_of_subset hsub
end MurtySimon
