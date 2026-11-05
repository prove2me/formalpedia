-- Prove2me | solution 1 for NicerEars.TJoin.theorem_25
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:26:15.512205+00:00
-- url     : https://prove2.me/submissions/0fdca110-6996-43ef-b7a2-86e8f4fb9258
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting
import Theorems.Thm_NicerEars_TJoin_exists_block_split
import Theorems.Thm_NicerEars_TJoin_theorem_25_twoVertexConnected
import Theorems.Thm_NicerEars_TJoin_proposition_4
import Theorems.Thm_NicerEars_TJoin_proposition_3

open Finset NicerEars.TJoin

namespace Sol25RedAux

theorem exists_adj_of_reachable {V : Type} {H : SimpleGraph V} {a b : V} (h : H.Reachable a b)
    (hab : a ≠ b) : ∃ w, H.Adj a w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hab
  | cons h _ => exact ⟨_, h⟩

theorem exists_T_part {V : Type} [DecidableEq V] (T W : Finset V) (v : V) (hv : v ∈ W) :
    ∃ T' : Finset W, Even #T' ∧ (T'.map (Function.Embedding.subtype _) = (T ∩ W).erase v ∨
      T'.map (Function.Embedding.subtype _) = insert v (T ∩ W)) := by
  have hA : ((T ∩ W).erase v).filter (· ∈ W) = (T ∩ W).erase v := by
    apply filter_true_of_mem
    intro x hx
    exact (mem_inter.mp (mem_of_mem_erase hx)).2
  have hB : (insert v (T ∩ W)).filter (· ∈ W) = insert v (T ∩ W) := by
    apply filter_true_of_mem
    intro x hx
    rcases mem_insert.mp hx with h | h
    · exact h ▸ hv
    · exact (mem_inter.mp h).2
  have hpar : #(insert v (T ∩ W)) = #((T ∩ W).erase v) + 1 := by
    by_cases hvT : v ∈ T ∩ W
    · rw [insert_eq_of_mem hvT, card_erase_add_one hvT]
    · rw [card_insert_of_notMem hvT, erase_eq_of_notMem hvT]
  by_cases hev : Even #((T ∩ W).erase v)
  · refine ⟨((T ∩ W).erase v).subtype (· ∈ W), ?_, Or.inl ?_⟩
    · rw [card_subtype, hA]; exact hev
    · rw [subtype_map, hA]
  · refine ⟨(insert v (T ∩ W)).subtype (· ∈ W), ?_, Or.inr ?_⟩
    · rw [card_subtype, hB, hpar]
      exact Nat.even_add_one.mpr hev
    · rw [subtype_map, hB]

theorem small_case {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TJoin.Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T)
    (hc : Fintype.card V ≤ 2) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      ∀ x : E → ℝ, G.LPTFeasible T x → (#F : ℝ) ≤ 3 / 2 * ∑ e, x e := by
  haveI : Nonempty V := hG.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have hTle : #T ≤ Fintype.card V := by
    rw [← card_univ]; exact card_le_univ T
  rcases (show Fintype.card V = 1 ∨ Fintype.card V = 2 by omega) with h1 | h2
  · -- one vertex
    have hT0 : T = ∅ := by
      have : #T = 0 := by
        rcases hT with ⟨r, hr⟩; omega
      exact card_eq_zero.mp this
    subst hT0
    have hsub : ∀ u w : V, u = w := by
      intro u w
      exact Fintype.card_le_one_iff.mp (by omega) u w
    refine ⟨∅, ⟨?_, ?_⟩, ?_⟩
    · intro v; simp
    · haveI : Nonempty V := hG.nonempty
      exact ⟨fun u w => by rw [hsub u w]⟩
    · intro x hx
      simp only [card_empty, Nat.cast_zero]
      have : 0 ≤ ∑ e, x e := sum_nonneg (fun e _ => hx.1 e)
      linarith
  · -- two vertices
    obtain ⟨a, b, hab, huniv⟩ := card_eq_two.mp (by rw [card_univ (α := V)]; exact h2)
    have hmem : ∀ u : V, u = a ∨ u = b := by
      intro u
      have : u ∈ ({a, b} : Finset V) := huniv ▸ mem_univ u
      simpa using this
    obtain ⟨w, hw⟩ := exists_adj_of_reachable (hG.preconnected a b) hab
    rw [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj] at hw
    obtain ⟨⟨e, -, he⟩, hne⟩ := hw
    have hwb : w = b := by
      rcases hmem w with h | h
      · exact absurd h.symm hne
      · exact h
    subst hwb
    have hin : ∀ u : V, u ∈ G.ends e := by
      intro u; rw [he]; rcases hmem u with h | h <;> simp [h]
    have hconn : ∀ F : Finset (E × Fin 2), (e, 0) ∈ F → (G.double.spanGraph F).Connected := by
      intro F hF
      have hadj : (G.double.spanGraph F).Adj a w := by
        rw [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨(e, 0), hF, he⟩, hab⟩
      refine ⟨fun u u' => ?_⟩
      rcases hmem u with rfl | rfl <;> rcases hmem u' with rfl | rfl
      · rfl
      · exact hadj.reachable
      · exact hadj.symm.reachable
      · rfl
    by_cases hT0 : T = ∅
    · subst hT0
      refine ⟨{(e, 0), (e, 1)}, ⟨?_, hconn _ (by simp)⟩, ?_⟩
      · intro v
        have : ({(e, 0), (e, 1)} : Finset (E × Fin 2)).filter
            (fun p => v ∈ G.double.ends p) = {(e, 0), (e, 1)} := by
          apply filter_true_of_mem
          intro p hp
          simp only [mem_insert, mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact hin v
        rw [this]
        simp
      · intro x hx
        have hcut := hx.2.1 {a} (singleton_nonempty a) (by
          intro h; have : w ∈ ({a} : Finset V) := h ▸ mem_univ w
          simp at this; exact hab this.symm) (by simp)
        have hle : ∑ e ∈ G.cut {a}, x e ≤ ∑ e, x e :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun e _ _ => hx.1 e)
        have hc2 : (#({(e, 0), (e, 1)} : Finset (E × Fin 2)) : ℝ) = 2 := by
          rw [card_pair (by simp)]; norm_num
        rw [hc2]; linarith
    · have hTu : T = univ := by
        apply eq_univ_of_card
        have : #T ≠ 0 := fun h => hT0 (card_eq_zero.mp h)
        rcases hT with ⟨r, hr⟩; omega
      refine ⟨{(e, 0)}, ⟨?_, hconn _ (by simp)⟩, ?_⟩
      · intro v
        have : ({(e, 0)} : Finset (E × Fin 2)).filter
            (fun p => v ∈ G.double.ends p) = {(e, 0)} := by
          apply filter_true_of_mem
          intro p hp
          simp only [mem_singleton] at hp
          subst hp; exact hin v
        rw [this, hTu]
        simp
      · intro x hx
        have := (proposition_3 G hG T hT).2 x hx
        rw [h2] at this
        simp only [card_singleton, Nat.cast_one]
        push_cast at this
        linarith

theorem main (n : ℕ) : ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TJoin.Graph V E), Fintype.card V ≤ n → G.IsConnected → ∀ T : Finset V, Even #T →
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      ∀ x : E → ℝ, G.LPTFeasible T x → (#F : ℝ) ≤ 3 / 2 * ∑ e, x e := by
  induction n with
  | zero =>
    intro V E _ _ _ _ G hn hG
    haveI : Nonempty V := hG.nonempty
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  | succ n ih =>
    intro V E _ _ _ _ G hn hG T hT
    by_cases h2 : G.IsTwoVertexConnected
    · exact theorem_25_twoVertexConnected G h2 T hT
    by_cases hc : Fintype.card V ≤ 2
    · exact small_case G hG T hT hc
    obtain ⟨v, V₁, V₂, E₁, E₂, hV, hV₁₂, hE, hE₁₂, hn₁, hn₂, h₁, h₂, hc₁, hc₂⟩ :=
      exists_block_split G hG h2 (by omega)
    have hv₁ : v ∈ V₁ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).1
    have hv₂ : v ∈ V₂ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).2
    obtain ⟨T₁, hT₁e, hT₁⟩ := exists_T_part T V₁ v hv₁
    obtain ⟨T₂, hT₂e, hT₂⟩ := exists_T_part T V₂ v hv₂
    have hlt : ∀ W : Finset V, W ≠ univ → Fintype.card W ≤ n := by
      intro W hW
      have : #W < #(univ : Finset V) := card_lt_card (ssubset_univ_iff.mpr hW)
      rw [card_univ] at this
      rw [Fintype.card_coe]; omega
    obtain ⟨F₁, hF₁, hb₁⟩ := ih V₁ E₁ (G.sub V₁ E₁ h₁) (hlt V₁ hn₁) hc₁ T₁ hT₁e
    obtain ⟨F₂, hF₂, hb₂⟩ := ih V₂ E₂ (G.sub V₂ E₂ h₂) (hlt V₂ hn₂) hc₂ T₂ hT₂e
    obtain ⟨-, hopt, -, -, hlp, -⟩ := proposition_4 G v V₁ V₂ E₁ E₂ hV hV₁₂ hE hE₁₂ h₁ h₂ hc₁ hc₂
      T hT T₁ T₂ ⟨hT₁e, hT₁⟩ ⟨hT₂e, hT₂⟩
    obtain ⟨F, hF, hFc⟩ := hopt F₁ F₂ hF₁ hF₂
    refine ⟨F, hF, fun x hx => ?_⟩
    obtain ⟨x₁, x₂, hx₁, hx₂, hs⟩ := hlp x hx
    have e1 := hb₁ x₁ hx₁
    have e2 := hb₂ x₂ hx₂
    have : (#F : ℝ) ≤ #F₁ + #F₂ := by exact_mod_cast hFc
    linarith

end Sol25RedAux

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TJoin.Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      ∀ x : E → ℝ, G.LPTFeasible T x → (#F : ℝ) ≤ 3 / 2 * ∑ e, x e :=
  Sol25RedAux.main _ V E G le_rfl hG T hT
