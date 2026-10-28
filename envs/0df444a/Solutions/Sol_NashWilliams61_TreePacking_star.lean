-- Prove2me | solution 1 for NashWilliams61.TreePacking.star
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:56:05.398095+00:00
-- url     : https://prove2.me/submissions/7ddb4554-be66-43eb-bc67-c63a1bf98d39

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_NashWilliams61_TreePacking_Couples

open NashWilliams61.TreePacking
open NagamochiIbaraki.EdgeConn
namespace Aux_NW_star
open NashWilliams61.TreePacking

theorem sub {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (k : ℕ) (X Y : Finset V) :
    Delta k ends (X ∩ Y) + Delta k ends (X ∪ Y) ≤ Delta k ends X + Delta k ends Y := by
  have h1 : edgesIn ends (X ∩ Y) = edgesIn ends X ∩ edgesIn ends Y := by
    ext e
    simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · intro h; exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩
    · intro h v hv; exact ⟨h.1 v hv, h.2 v hv⟩
  have h2 : edgesIn ends X ∪ edgesIn ends Y ⊆ edgesIn ends (X ∪ Y) := by
    intro e
    simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rintro (h | h) v hv
    · exact Or.inl (h v hv)
    · exact Or.inr (h v hv)
  have h3 := Finset.card_union_add_card_inter (edgesIn ends X) (edgesIn ends Y)
  have h4 := Finset.card_le_card h2
  have h5 := Finset.card_union_add_card_inter X Y
  rw [← h1] at h3
  unfold Delta
  have h3' : ((edgesIn ends X ∪ edgesIn ends Y).card : ℤ) + ((edgesIn ends (X ∩ Y)).card : ℤ)
      = ((edgesIn ends X).card : ℤ) + ((edgesIn ends Y).card : ℤ) := by exact_mod_cast h3
  have h4' : ((edgesIn ends X ∪ edgesIn ends Y).card : ℤ) ≤ ((edgesIn ends (X ∪ Y)).card : ℤ) := by
    exact_mod_cast h4
  have h5' : ((X ∪ Y).card : ℤ) + ((X ∩ Y).card : ℤ) = (X.card : ℤ) + (Y.card : ℤ) := by
    exact_mod_cast h5
  have : (k : ℤ) * (((X ∩ Y).card : ℤ) - 1) + (k : ℤ) * (((X ∪ Y).card : ℤ) - 1)
      = (k : ℤ) * ((X.card : ℤ) - 1) + (k : ℤ) * ((Y.card : ℤ) - 1) := by
    linear_combination (k : ℤ) * h5'
  linarith

theorem compl_sum {V : Type} [Fintype V] [DecidableEq V] (g : V → ℕ) (X Y : Finset V) :
    ∑ v ∈ Finset.univ \ (X ∩ Y), (g v : ℤ) + ∑ v ∈ Finset.univ \ (X ∪ Y), (g v : ℤ)
      = ∑ v ∈ Finset.univ \ X, (g v : ℤ) + ∑ v ∈ Finset.univ \ Y, (g v : ℤ) := by
  rw [Finset.sdiff_inter_distrib_right, Finset.sdiff_union_distrib]
  exact Finset.sum_union_inter

end Aux_NW_star

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k)
    (g : V → ℕ) (s : ℕ) (X Y : Finset V) (hXY : (X ∩ Y).Nonempty) :
    (IsCouple k ends g → Delta k ends X = 0 → Delta k ends Y = 0 →
        Delta k ends (X ∩ Y) = 0 ∧ Delta k ends (X ∪ Y) = 0) ∧
      (IsGood k ends g s → Gamma k ends g s X = 0 → Gamma k ends g s Y = 0 →
        Gamma k ends g s (X ∩ Y) = 0 ∧ Gamma k ends g s (X ∪ Y) = 0) := by
  have hU : (X ∪ Y).Nonempty := by
    obtain ⟨x, hx⟩ := hXY; exact ⟨x, Finset.mem_union_left _ (Finset.mem_inter.mp hx).1⟩
  have hs := Aux_NW_star.sub ends k X Y
  refine ⟨fun hc hX hY => ?_, fun hg hX hY => ?_⟩
  · have a := hc _ hXY
    have b := hc _ hU
    constructor <;> linarith
  · have a := hg.2.2 _ hXY
    have b := hg.2.2 _ hU
    have hcs := Aux_NW_star.compl_sum g X Y
    unfold Gamma at hX hY ⊢
    constructor <;> linarith
