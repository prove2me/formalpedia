-- Prove2me | solution 2 for Menger.exists_separator_and_paths_of_not_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:55:52.458078+00:00
-- url     : https://prove2.me/submissions/2db1c065-6ee4-43fe-8e10-48a1d0087954

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Definitions.Def_MengerHamilton_Menger
public import Theorems.Thm_Menger_card_le_of_separates
public import Theorems.Thm_Menger_exists_separator_and_paths
public import Theorems.Thm_Menger_Aux_Sep_symm
public import Theorems.Thm_Menger_Aux_start_eq_of_isolated


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger
variable {V : Type*}
namespace Menger
theorem _root_.solution [Finite V] (G : SimpleGraph V)
    {s t : V} (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ X : Finset V, s ∉ X ∧ t ∉ X ∧ (∀ p : G.Walk s t, ∃ x ∈ X, x ∈ p.support) ∧
      ∃ p : Fin X.card → G.Walk s t, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∈ (p j).support → x = s ∨ x = t := by
  classical
  have := Fintype.ofFinite V
  set H := G.deleteEdges {e | s ∈ e ∨ t ∈ e} with hH
  set A := G.neighborFinset s with hA
  set B := G.neighborFinset t with hB
  have hHs : ∀ w, ¬ H.Adj s w := by intro w h; simp [hH] at h
  have hHt : ∀ w, ¬ H.Adj t w := by intro w h; simp [hH] at h
  have hsA : s ∉ A := by simp [hA]
  have htA : t ∉ A := by simpa [hA] using hadj
  have hnot : ∀ {a b : V} (q : H.Walk a b), a ∈ A → s ∉ q.support ∧ t ∉ q.support := by
    intro a b q ha
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact hsA (Aux.start_eq_of_isolated hHs q h ▸ ha)
    · exact htA (Aux.start_eq_of_isolated hHt q h ▸ ha)
  obtain ⟨X, hX, a, b, p, hp, hd⟩ := exists_separator_and_paths H A B
  have herase : ∀ v, v ∈ X → (v = s ∨ v = t) → False := by
    intro v hv hvst
    have hsep' : Separates H A B (X.erase v) := by
      intro a' ha' b' hb' q
      obtain ⟨x, hx, hxq⟩ := hX a' ha' b' hb' q
      refine ⟨x, Finset.mem_erase.2 ⟨?_, hx⟩, hxq⟩
      rintro rfl
      rcases hvst with rfl | rfl
      · exact (hnot q ha').1 hxq
      · exact (hnot q ha').2 hxq
    have := card_le_of_separates hsep' a b p (fun i => (hp i).1) (fun i => (hp i).2.1) hd
    rw [Finset.card_erase_of_mem hv] at this
    have : 0 < X.card := Finset.card_pos.2 ⟨v, hv⟩
    omega
  refine ⟨X, fun h => herase s h (Or.inl rfl), fun h => herase t h (Or.inr rfl), ?_, ?_⟩
  · have key : ∀ {u v : V} (q : G.Walk u v), v = t →
        (u = s ∨ ∃ a ∈ A, ∃ r : H.Walk a u, ∀ w ∈ r.support, w ∉ X) →
        (∀ w ∈ q.support, w ∉ X) → False := by
      intro u v q
      induction q with
      | nil =>
        rintro rfl (h | ⟨a', ha', r, hr⟩) -
        · exact hst h.symm
        · have := Aux.start_eq_of_isolated hHt r r.end_mem_support
          subst this
          exact htA ha'
      | @cons u w v h q ih =>
        rintro rfl hu hq
        apply ih rfl ?_ (fun x hx => hq x (by simp [hx]))
        have hwX : w ∉ X := hq w (by simp)
        by_cases hws : w = s
        · exact Or.inl hws
        rcases hu with rfl | ⟨a', ha', r, hr⟩
        · exact Or.inr ⟨w, by simpa [hA] using h, Walk.nil, by simpa using hwX⟩
        · have hus : u ≠ s := fun hus => (hnot r ha').1 (hus ▸ r.end_mem_support)
          have hut : u ≠ v := fun hut => (hnot r ha').2 (hut ▸ r.end_mem_support)
          by_cases hwt : w = v
          · subst hwt
            obtain ⟨x, hx, hxr⟩ := hX a' ha' u (by simpa [hB] using h.symm) r
            exact (hr x hxr hx).elim
          · have hadjH : H.Adj u w := by
              simp only [hH, deleteEdges_adj, Set.mem_ofPred_eq, Sym2.mem_iff, not_or]
              exact ⟨h, ⟨Ne.symm hus, Ne.symm hws⟩, Ne.symm hut, Ne.symm hwt⟩
            refine Or.inr ⟨a', ha', r.concat hadjH, fun x hx => ?_⟩
            rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hr x hx
            · exact hwX
    intro q
    by_contra hcon
    push Not at hcon
    exact key q rfl (Or.inl rfl) (fun w hw hwX => hcon w hwX hw)
  · have hle : H ≤ G := G.deleteEdges_le _
    have hsa : ∀ i, G.Adj s (a i) := fun i => by simpa [hA] using (hp i).1
    have hbt : ∀ i, G.Adj (b i) t := fun i => (by simpa [hB] using (hp i).2.1 : G.Adj t (b i)).symm
    refine ⟨fun i => Walk.cons (hsa i) (((p i).mapLe hle).concat (hbt i)), fun i => ?_,
      fun i j hij x hx hx' => ?_⟩
    · have h1 := hnot (p i) (hp i).1
      refine Walk.IsPath.cons (((hp i).2.2.mapLe hle).concat ?_ _) ?_
      · simpa using h1.2
      · simp only [Walk.support_concat, Walk.support_mapLe_eq_support, List.mem_append,
          List.mem_singleton, not_or]
        exact ⟨h1.1, hst⟩
    · simp only [Walk.support_cons, Walk.support_concat, Walk.support_mapLe_eq_support,
        List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx hx'
      rcases hx with h | h | h
      · exact Or.inl h
      · rcases hx' with h' | h' | h'
        · exact Or.inl h'
        · exact absurd h' (hd i j hij x h)
        · exact Or.inr h'
      · exact Or.inr h
end Menger
