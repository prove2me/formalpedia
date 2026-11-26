-- Prove2me | solution 1 for MurtySimon.leaf_analysis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:46.65656+00:00
-- url     : https://prove2.me/submissions/db9b0754-e73b-4b6d-853f-750b86d57743

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_mate_spec
public import Theorems.Thm_MurtySimon_IsEdgeMatching_mate_mate
public import Theorems.Thm_MurtySimon_covered_mate
public import Theorems.Thm_MurtySimon_IsEdgeMatching_adj_mate
public import Theorems.Thm_MurtySimon_IsEdgeMatching_mate_ne
public import Theorems.Thm_MurtySimon_IsMaximalEdgeMatching_covered
public import Theorems.Thm_MurtySimon_isMid_of_isCrit
public import Theorems.Thm_MurtySimon_two_le_compWt_of_safe
public import Theorems.Thm_MurtySimon_two_le_compWt_of_two
public import Theorems.Thm_MurtySimon_exit_of_left
public import Theorems.Thm_MurtySimon_IsMid_isCrit
public import Theorems.Thm_MurtySimon_IsMid_ne_left
public import Theorems.Thm_MurtySimon_IsMid_ne_right
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_OnPath_isCrit
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_aux_adj
public import Theorems.Thm_MurtySimon_aux_adj_cases
public import Theorems.Thm_MurtySimon_comp_count
public import Theorems.Thm_MurtySimon_mem_Lt
public import Theorems.Thm_MurtySimon_mem_Rt
public import Theorems.Thm_MurtySimon_mem_neighborFinset_right
public import Theorems.Thm_MurtySimon_not_mem_Rt_of_mem_Lt
public import Theorems.Thm_MurtySimon_onPath_iff


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
theorem _root_.solution (hmax : IsMaximalEdgeMatching G M) {ℓ : Sym2 V} (hℓL : ℓ ∈ Lt G M)
    (hℓC : (aux G M).connectedComponentMk ℓ = C) (hℓd : #((aux G M).neighborFinset ℓ) = 1) :
    2 ≤ compWt C ∨ ∃ p ∈ exits G M, compOf G M p = C ∧ Recovers (G := G) (M := M) p ℓ := by
  obtain ⟨f, hf⟩ := card_eq_one.1 hℓd
  have hℓf : (aux G M).Adj ℓ f := (mem_neighborFinset _ _ _).1 (hf ▸ mem_singleton_self f)
  have hnbr : ∀ g, (aux G M).Adj ℓ g → g = f := fun g hg =>
    mem_singleton.1 (hf ▸ (mem_neighborFinset _ _ _).2 hg)
  have hfC : (aux G M).connectedComponentMk f = C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hℓf).symm.trans hℓC
  have hon : OnPath G ℓ f := by
    rcases aux_adj_cases hℓf with h | h
    · exact h.2.2
    · exact absurd h.2.1 (not_mem_Rt_of_mem_Lt hℓL)
  -- orient the critical 2-path as `(x, u, y)` with `ℓ = uy`
  obtain ⟨x, y, u, rfl, hm, hℓ⟩ : ∃ x y u, f = s(x, y) ∧ IsMid G x y u ∧ ℓ = s(u, y) := by
    obtain ⟨x, y, u, rfl, hm, rfl⟩ := hon
    exact ⟨y, x, u, Sym2.eq_swap, hm.symm, Sym2.eq_swap⟩
  subst hℓ
  have hfR : s(x, y) ∈ Rt G := mem_Rt.2 hm.isCrit
  -- both edges of the critical 2-path lie in `𝓘'`
  have hdeg := (comp_count M C).2 hC |>.1 s(x, y) hfR hfC
  have hxuM : s(x, u) ∉ M := by
    intro hin
    have hsub : (aux G M).neighborFinset s(x, y) ⊆ {s(u, y)} := by
      intro e he
      obtain ⟨h1 | h1, h2⟩ := (mem_neighborFinset_right hm).1 he
      · exact absurd (h1 ▸ hin) h2
      · exact mem_singleton.2 h1
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
  have huyM : s(u, y) ∉ M := (mem_Lt.1 hℓL).2
  have hxu : G.Adj x u := hm.2.2.1
  have huy : G.Adj u y := hm.2.2.2.1
  have hxuL : s(x, u) ∈ Lt G M := mem_Lt.2 ⟨hxu, hxuM⟩
  have hxuC : (aux G M).connectedComponentMk s(x, u) = C := by
    rw [← hfC]
    apply ConnectedComponent.connectedComponentMk_eq_of_adj
    rw [aux_adj]
    exact Or.inl ⟨hxuM, (onPath_iff hm).2 (Or.inl rfl)⟩
  have hxy : x ≠ y := hm.1
  have hux : u ≠ x := hm.ne_left
  have huy' : u ≠ y := hm.ne_right
  -- Case 1: `u` covered
  have case1 : Covered M u →
      ((mate M u, x) ∈ exits G M ∧ compOf G M (mate M u, x) = C) ∨
      ((mate M u, y) ∈ exits G M ∧ compOf G M (mate M u, y) = C ∧
        Recovers (G := G) (M := M) (mate M u, y) s(u, y)) := by
    intro hu
    have hmm : mate M (mate M u) = u := hM.mate_mate hu
    have hu'x : mate M u ≠ x := fun h => hxuM (by rw [Sym2.eq_swap, ← h]; exact mate_spec hu)
    have hu'y : mate M u ≠ y := fun h => huyM (h ▸ mate_spec hu)
    by_cases h1 : G.Adj (mate M u) x
    · have h2 : ¬ G.Adj (mate M u) y := by
        intro h2
        exact hM.mate_ne hu (hm.2.2.2.2 _ h1.symm h2)
      right
      obtain ⟨hp, hpC⟩ := exit_of_left hM hC (covered_mate hu) hu'y h2
        (by rw [hmm]; exact hℓL) (by rw [hmm]; exact hℓC)
      exact ⟨hp, hpC, Or.inl (by rw [hmm])⟩
    · left
      exact exit_of_left hM hC (covered_mate hu) hu'x h1
        (by rw [hmm, Sym2.eq_swap]; exact hxuL) (by rw [hmm, Sym2.eq_swap]; exact hxuC)
  -- Case 2: `x` covered
  have case2 : Covered M x →
      ((mate M x, u) ∈ exits G M ∧ compOf G M (mate M x, u) = C) ∨
      ((mate M x, y) ∈ exits G M ∧ compOf G M (mate M x, y) = C ∧
        Recovers (G := G) (M := M) (mate M x, y) s(u, y)) := by
    intro hx
    have hmm : mate M (mate M x) = x := hM.mate_mate hx
    have hx'u : mate M x ≠ u := fun h => hxuM (h ▸ mate_spec hx)
    have hx'y : mate M x ≠ y := fun h => hm.2.1 (h ▸ hM.adj_mate hx)
    by_cases h1 : G.Adj (mate M x) u
    · right
      have h2 : ¬ G.Adj (mate M x) y := by
        intro h2
        exact hx'u (hm.2.2.2.2 _ (hM.adj_mate hx) h2)
      have hnc : ¬ IsCrit G s(mate M x, y) := by
        intro hcrit
        have hm' : IsMid G (mate M x) y u := isMid_of_isCrit hcrit h1 huy
        have hadj : (aux G M).Adj s(u, y) s(mate M x, y) :=
          aux_adj.2 (Or.inl ⟨huyM, (onPath_iff hm').2 (Or.inr rfl)⟩)
        have := hnbr _ hadj
        exact hM.mate_ne hx (Sym2.congr_left.1 this)
      refine ⟨mem_filter.2 ⟨mem_univ _, ?_, hnc, covered_mate hx, ?_⟩, ?_, ?_⟩
      · rw [mem_edgeSet, compl_adj]; exact ⟨hx'y, h2⟩
      · rw [hmm]; exact mem_union_right _ hfR
      · simp only [compOf, hmm]; exact hfC
      · exact Or.inr ⟨x, u, by rw [hmm], hm, rfl⟩
    · left
      exact exit_of_left hM hC (covered_mate hx) hx'u h1 (by rw [hmm]; exact hxuL)
        (by rw [hmm]; exact hxuC)
  have hne1 : (mate M u, x) ≠ (mate M x, u) := fun h => hux (Prod.ext_iff.1 h).2.symm
  have hne2 : (mate M u, x) ≠ (mate M x, y) := fun h => hxy (Prod.ext_iff.1 h).2
  have hne3 : (mate M x, u) ≠ (mate M u, y) := fun h => huy' (Prod.ext_iff.1 h).2
  rcases hmax.covered hxu hxuM with hx | hu
  · rcases case2 hx with ⟨hp, hpC⟩ | ⟨hp, hpC, hrec⟩
    · -- Case 2a
      by_cases hu : Covered M u
      · left
        rcases case1 hu with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · exact two_le_compWt_of_two hq hqC hp hpC hne1
        · exact two_le_compWt_of_two hp hpC hq hqC hne3
      · exact Or.inl (two_le_compWt_of_safe hp hpC hu)
    · by_cases hu : Covered M u
      · rcases case1 hu with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · -- Case 1a with `x` covered
          exact Or.inl (two_le_compWt_of_two hq hqC hp hpC hne2)
        · exact Or.inr ⟨_, hp, hpC, hrec⟩
      · exact Or.inr ⟨_, hp, hpC, hrec⟩
  · rcases case1 hu with ⟨hp, hpC⟩ | ⟨hp, hpC, hrec⟩
    · -- Case 1a
      by_cases hx : Covered M x
      · left
        rcases case2 hx with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · exact two_le_compWt_of_two hp hpC hq hqC hne1
        · exact two_le_compWt_of_two hp hpC hq hqC hne2
      · exact Or.inl (two_le_compWt_of_safe hp hpC hx)
    · by_cases hx : Covered M x
      · rcases case2 hx with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · exact Or.inl (two_le_compWt_of_two hq hqC hp hpC hne3)
        · exact Or.inr ⟨_, hp, hpC, hrec⟩
      · exact Or.inr ⟨_, hp, hpC, hrec⟩
end MurtySimon
