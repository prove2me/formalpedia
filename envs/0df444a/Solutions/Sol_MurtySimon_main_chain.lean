-- Prove2me | solution 1 for MurtySimon.main_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:55.705715+00:00
-- url     : https://prove2.me/submissions/092eaef7-b52a-41e5-831b-8bed1f39f3c3

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_sum_wt_le
public import Theorems.Thm_MurtySimon_two_le_compWt
public import Theorems.Thm_MurtySimon_sum_cA
public import Theorems.Thm_MurtySimon_sum_cB
public import Theorems.Thm_MurtySimon_sum_compWt
public import Theorems.Thm_MurtySimon_comp_count


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
theorem _root_.solution (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) :
    (#(Lt G M) : ℤ) - #(Rt G) =
      ∑ C, ((cA G M C : ℤ) - cB G M C) ∧
    (∀ C, ((cA G M C : ℤ) - cB G M C) ≤ if cA G M C = cB G M C + 1 then 1 else 0) ∧
    2 * #((univ : Finset (aux G M).ConnectedComponent).filter fun C => cA G M C = cB G M C + 1)
      + ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
          (fun C => ¬ cA G M C = cB G M C + 1), compWt (G := G) (M := M) C
      ≤ 2 * #(Nc G) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_sub_distrib, ← sum_cA, ← sum_cB]; push_cast; ring
  · intro C
    have := (comp_count M C).1
    split_ifs with h <;> omega
  · have h1 : 2 * #((univ : Finset (aux G M).ConnectedComponent).filter
        fun C => cA G M C = cB G M C + 1) ≤
        ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
          (fun C => cA G M C = cB G M C + 1), compWt (G := G) (M := M) C := by
      rw [mul_comm, ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun C hC => two_le_compWt hmax.1 (mem_filter.1 hC).2 hmax hG
    have h2 := sum_filter_add_sum_filter_not (univ : Finset (aux G M).ConnectedComponent)
      (fun C => cA G M C = cB G M C + 1) (compWt (G := G) (M := M))
    rw [sum_compWt] at h2
    have h3 := sum_wt_le (G := G) (M := M)
    omega
end MurtySimon
