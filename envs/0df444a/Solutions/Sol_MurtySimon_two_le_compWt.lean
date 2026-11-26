-- Prove2me | solution 1 for MurtySimon.two_le_compWt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:00.930241+00:00
-- url     : https://prove2.me/submissions/e9fddb6c-9064-4375-b786-490a32210704

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_two_le_compWt_of_two
public import Theorems.Thm_MurtySimon_Recovers_unique
public import Theorems.Thm_MurtySimon_two_le_compWt_single
public import Theorems.Thm_MurtySimon_leaf_analysis
public import Theorems.Thm_MurtySimon_IsMid_unique
public import Theorems.Thm_MurtySimon_comp_count
public import Theorems.Thm_MurtySimon_mem_Lt


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
variable (hM : IsEdgeMatching G M) {C : (aux G M).ConnectedComponent}
  (hC : cA G M C = cB G M C + 1)
include hM hC
namespace MurtySimon
theorem _root_.solution (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) : 2 ≤ compWt C := by
  by_cases h1 : cA G M C = 1
  · exact two_le_compWt_single hM hC hmax hG h1
  have h2 : 2 ≤ cA G M C := by omega
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hC₁, hC₂, hd₁, hd₂⟩ := (comp_count M C).2 hC |>.2 h2
  rcases leaf_analysis hM hC hmax hl₁ hC₁ hd₁ with h | ⟨p, hp, hpC, hrp⟩
  · exact h
  rcases leaf_analysis hM hC hmax hl₂ hC₂ hd₂ with h | ⟨q, hq, hqC, hrq⟩
  · exact h
  refine two_le_compWt_of_two hp hpC hq hqC ?_
  rintro rfl
  exact hne (hrp.unique hrq (mem_Lt.1 hl₁).1 (mem_Lt.1 hl₂).1)
end MurtySimon
