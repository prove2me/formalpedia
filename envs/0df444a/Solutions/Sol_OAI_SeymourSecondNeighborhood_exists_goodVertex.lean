-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.exists_goodVertex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T20:33:38.348151+00:00
-- url     : https://prove2.me/submissions/2e8e6e02-a3b9-4e6f-bf5f-e3b490f0efc1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image
import Theorems.Thm_OAI_SeymourSecondNeighborhood_lemma_2_2
import Theorems.Thm_OAI_SeymourSecondNeighborhood_lemma_2_3
import Theorems.Thm_OAI_SeymourSecondNeighborhood_prop_4_1

set_option autoImplicit false
open Finset

namespace OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_exists_goodVertex

universe u

-- Number of arcs of a relation on a finite type.
open Classical in
noncomputable def arcCount {V : Type u} [Fintype V] (r : V → V → Prop) : ℕ :=
  (univ.filter (fun p : V × V => r p.1 p.2)).card

-- Removing at least one arc strictly decreases the arc count.
open Classical in
theorem arcCount_lt {V : Type u} [Fintype V] (r r' : V → V → Prop)
    (hsub : ∀ a b, r' a b → r a b) (hmiss : ∃ a b, r a b ∧ ¬ r' a b) :
    arcCount r' < arcCount r := by
  unfold arcCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hsub _ _ hp
  · intro heq
    obtain ⟨a, b, hab, hnab⟩ := hmiss
    have hmem : (a, b) ∈ univ.filter (fun p : V × V => r' p.1 p.2) := by
      rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hnab hmem

/-- A subrelation of an oriented relation is oriented. -/
theorem isOriented_of_sub {V : Type u} (r r' : V → V → Prop) (hr : IsOriented r)
    (hsub : ∀ a b, r' a b → r a b) : IsOriented r' :=
  ⟨fun v hv => hr.loopless v (hsub v v hv),
   fun {u v} huv hvu => hr.asymmetric (hsub u v huv) (hsub v u hvu)⟩

/-- Main auxiliary statement, by strong induction on the number of vertices. -/
theorem aux : ∀ (n : ℕ) (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V],
    Fintype.card V = n → ∀ r : V → V → Prop, IsOriented r → ∃ v, GoodVertex r v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hcard r hr
  by_contra h
  have hbad0 : ∀ v, ¬ GoodVertex r v := fun v hv => h ⟨v, hv⟩
  classical
  -- the set of arc counts of bad subrelations of `r`
  let P : ℕ → Prop := fun k => ∃ r' : V → V → Prop,
    (∀ a b, r' a b → r a b) ∧ (∀ v, ¬ GoodVertex r' v) ∧ arcCount r' = k
  have hP : ∃ k, P k := ⟨arcCount r, r, fun _ _ hab => hab, hbad0, rfl⟩
  obtain ⟨r₀, hsub, hbad, hk⟩ := Nat.find_spec hP
  have hr₀ : IsOriented r₀ := isOriented_of_sub r r₀ hr hsub
  -- arc-minimality
  have hmin_arcs : ∀ r'' : V → V → Prop, (∀ a b, r'' a b → r₀ a b) →
      (∃ a b, r₀ a b ∧ ¬ r'' a b) → ∃ v, GoodVertex r'' v := by
    intro r'' hsub' hmiss
    by_contra hno
    have hno' : ∀ v, ¬ GoodVertex r'' v := fun v hv => hno ⟨v, hv⟩
    have hsub'' : ∀ a b, r'' a b → r a b := fun a b hab => hsub a b (hsub' a b hab)
    have hlt : arcCount r'' < Nat.find hP := by
      rw [← hk]
      exact arcCount_lt r₀ r'' hsub' hmiss
    exact Nat.find_min hP hlt ⟨r'', hsub'', hno', rfl⟩
  -- order-minimality
  have hmin_order : ∀ W : Finset V, W.Nonempty → W ≠ univ →
      ∃ v : W, GoodVertex (fun a b : W => r₀ a b) v := by
    intro W hW hWu
    have hlt : Fintype.card W < n := by
      rw [← hcard, Fintype.card_coe, ← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hWu)
    have : Nonempty W := hW.to_subtype
    exact ih _ hlt W rfl (fun a b : W => r₀ a b)
      ⟨fun v hv => hr₀.loopless v hv, fun {u v} huv hvu => hr₀.asymmetric huv hvu⟩
  obtain ⟨hin, hdef⟩ := lemma_2_2 r₀ hr₀ hbad hmin_arcs hmin_order
  have hm : Fintype.card V < n + 1 := by omega
  obtain ⟨hor, hin', hexp⟩ := lemma_2_3 r₀ hr₀ hin hdef (n + 1) hm
  have : Nonempty (V × Fin (n + 1)) := ⟨(Classical.arbitrary V, ⟨0, by omega⟩)⟩
  exact prop_4_1 (blowup r₀ (n + 1)) hor hin' hexp

end OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_exists_goodVertex

open OAI.SeymourSecondNeighborhood in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (r : V → V → Prop)
    (hr : IsOriented r) : ∃ v, GoodVertex r v :=
  OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_exists_goodVertex.aux
    (Fintype.card V) V rfl r hr
