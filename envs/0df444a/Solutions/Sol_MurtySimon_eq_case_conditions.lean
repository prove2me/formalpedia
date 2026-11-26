-- Prove2me | solution 1 for MurtySimon.eq_case_conditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:13:57.483131+00:00
-- url     : https://prove2.me/submissions/58d59c42-fbb6-4a38-b0c2-4c1991b561ba

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_one_le_compWt
public import Theorems.Thm_MurtySimon_main_chain

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
theorem _root_.solution (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G)
    (heq : #(Lt G M) = #(Rt G) + #(Nc G)) :
    (∀ C, cB G M C ≤ cA G M C) ∧
    (∀ C, cA G M C = cB G M C → ∀ p ∈ exits G M, compOf G M p ≠ C) := by
  obtain ⟨h1, h2, h3⟩ := main_chain hmax hG
  set L := (univ : Finset (aux G M).ConnectedComponent).filter fun C => cA G M C = cB G M C + 1
  have hsum : ∑ C, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) = #L := by rw [sum_boole]
  refine ⟨fun C0 => ?_, fun C0 hC0 p hp hpC => ?_⟩
  · by_contra hlt
    push Not at hlt
    have h4 : ∑ C, ((cA G M C : ℤ) - cB G M C) ≤
        ∑ C, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) - 1 := by
      rw [← sum_erase_add _ _ (mem_univ C0), ← sum_erase_add _ _ (mem_univ C0)]
      have : ∑ C ∈ univ.erase C0, ((cA G M C : ℤ) - cB G M C) ≤
          ∑ C ∈ univ.erase C0, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) :=
        sum_le_sum fun C _ => h2 C
      have hC0 : ¬ cA G M C0 = cB G M C0 + 1 := by omega
      simp only [hC0, if_false]
      omega
    have := h3
    have h5 : 0 ≤ ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun C => ¬ cA G M C = cB G M C + 1), (compWt (G := G) (M := M) C : ℤ) :=
      sum_nonneg fun _ _ => by positivity
    omega
  · have hC0L : C0 ∉ L := by simp [L]; omega
    have h4 : 1 ≤ ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun C => ¬ cA G M C = cB G M C + 1), compWt (G := G) (M := M) C :=
      (one_le_compWt hp hpC).trans
        (single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨mem_univ _, by omega⟩))
    have h5 : ∑ C, ((cA G M C : ℤ) - cB G M C) ≤ #L := by
      rw [← hsum]; exact sum_le_sum fun C _ => h2 C
    omega
end MurtySimon
