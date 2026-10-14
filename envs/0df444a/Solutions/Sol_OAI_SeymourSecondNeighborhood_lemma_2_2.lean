-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T21:07:10.880561+00:00
-- url     : https://prove2.me/submissions/b30eddaf-b602-438e-b2c9-b828ec0c1fc6

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

set_option autoImplicit false
open Finset

namespace OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_lemma_2_2

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem mem_firstNeighbors (r : V → V → Prop) (v w : V) :
    w ∈ firstNeighbors r v ↔ r v w := by
  simp only [firstNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_secondNeighbors (r : V → V → Prop) (v w : V) :
    w ∈ secondNeighbors r v ↔ w ≠ v ∧ ¬ r v w ∧ ∃ u, r v u ∧ r u w := by
  simp only [secondNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq V] in
theorem mem_fwd (r : V → V → Prop) (U : Finset V) (y : V) :
    y ∈ fwd r U ↔ ∃ x ∈ U, r x y := by
  simp only [fwd, Finset.mem_filter, Finset.mem_univ, true_and]

theorem fwd_union (r : V → V → Prop) (A B : Finset V) :
    fwd r (A ∪ B) = fwd r A ∪ fwd r B := by
  ext y
  simp only [mem_fwd, Finset.mem_union]
  constructor
  · rintro ⟨x, hx | hx, h⟩
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨x, Or.inl hx, h⟩
    · exact ⟨x, Or.inr hx, h⟩

omit [DecidableEq V] in
theorem fwd_mono (r : V → V → Prop) {A B : Finset V} (h : A ⊆ B) : fwd r A ⊆ fwd r B := by
  intro y hy
  rw [mem_fwd] at hy ⊢
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, h hx, hxy⟩

omit [DecidableEq V] in
theorem fwd_empty (r : V → V → Prop) : fwd r ∅ = ∅ := by
  ext y
  simp only [mem_fwd, Finset.notMem_empty, false_and, exists_false]

/-- Goodness in an induced subgraph containing all out-neighbours transfers to the whole graph. -/
theorem good_of_restrict (r : V → V → Prop) (W : Finset V) (u : V) (hu : u ∈ W)
    (h1 : ∀ w, r u w → w ∈ W)
    (hg : GoodVertex (fun a b : W => r a b) ⟨u, hu⟩) : GoodVertex r u := by
  unfold GoodVertex at hg ⊢
  have e1 : (firstNeighbors (fun a b : W => r a b) ⟨u, hu⟩).image Subtype.val
      = firstNeighbors r u := by
    ext w
    simp only [Finset.mem_image, mem_firstNeighbors]
    constructor
    · rintro ⟨⟨w', hw'⟩, hr, rfl⟩
      exact hr
    · intro hr
      exact ⟨⟨w, h1 w hr⟩, hr, rfl⟩
  have e2 : (secondNeighbors (fun a b : W => r a b) ⟨u, hu⟩).image Subtype.val
      ⊆ secondNeighbors r u := by
    intro w hw
    simp only [Finset.mem_image, mem_secondNeighbors] at hw ⊢
    obtain ⟨⟨w', hw'⟩, ⟨hne, hnr, ⟨⟨u', hu'⟩, h1', h2'⟩⟩, rfl⟩ := hw
    refine ⟨?_, hnr, u', h1', h2'⟩
    intro h
    apply hne
    exact Subtype.ext h
  have c1 := Finset.card_image_of_injective
    (firstNeighbors (fun a b : W => r a b) ⟨u, hu⟩) (Subtype.val_injective (p := fun x => x ∈ W))
  have c2 := Finset.card_image_of_injective
    (secondNeighbors (fun a b : W => r a b) ⟨u, hu⟩) (Subtype.val_injective (p := fun x => x ∈ W))
  rw [e1] at c1
  have c3 := Finset.card_le_card e2
  omega

/-- If `v` keeps all its out-arcs when passing from `r` to the subrelation `r'`, goodness in `r'`
transfers to goodness in `r`. -/
theorem good_of_sub_eq (r r' : V → V → Prop) (hsub : ∀ a b, r' a b → r a b) (v : V)
    (heq : ∀ w, r v w ↔ r' v w) (hg : GoodVertex r' v) : GoodVertex r v := by
  unfold GoodVertex at hg ⊢
  have e1 : firstNeighbors r v = firstNeighbors r' v := by
    ext w
    simp only [mem_firstNeighbors]
    exact heq w
  have e2 : secondNeighbors r' v ⊆ secondNeighbors r v := by
    intro w hw
    simp only [mem_secondNeighbors] at hw ⊢
    obtain ⟨hne, hnr, u, h1, h2⟩ := hw
    exact ⟨hne, fun h => hnr ((heq w).1 h), u, hsub _ _ h1, hsub _ _ h2⟩
  rw [e1]
  exact le_trans hg (Finset.card_le_card e2)

/-- Part (1): positive in-degree. -/
theorem posIndeg (r : V → V → Prop) (hr : IsOriented r)
    (hbad : ∀ v, ¬ GoodVertex r v)
    (hmin_order : ∀ W : Finset V, W.Nonempty → W ≠ univ →
      ∃ v : W, GoodVertex (fun a b : W => r a b) v) : PosIndeg r := by
  intro v
  by_contra hno
  have hno' : ∀ u, ¬ r u v := fun u h => hno ⟨u, h⟩
  by_cases hW : (univ.erase v).Nonempty
  · have hWu : univ.erase v ≠ univ := by
      intro h
      have : v ∈ univ.erase v := by rw [h]; exact Finset.mem_univ v
      exact (Finset.mem_erase.1 this).1 rfl
    obtain ⟨⟨u, hu⟩, hgu⟩ := hmin_order _ hW hWu
    apply hbad u
    refine good_of_restrict r _ u hu ?_ hgu
    intro w hw
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ w⟩
    rintro rfl
    exact hno' u hw
  · apply hbad v
    unfold GoodVertex
    have : firstNeighbors r v = ∅ := by
      ext w
      simp only [mem_firstNeighbors, Finset.notMem_empty, iff_false]
      intro hw
      have hwv : w = v := by
        by_contra hne
        apply hW
        exact ⟨w, Finset.mem_erase.2 ⟨hne, Finset.mem_univ w⟩⟩
      subst hwv
      exact hr.loopless w hw
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

omit [Fintype V] [DecidableEq V] in
/-- The relation `r` with all arcs from `S` into `D` deleted. -/
def del (r : V → V → Prop) (S D : Finset V) : V → V → Prop :=
  fun a b => r a b ∧ ¬ (a ∈ S ∧ b ∈ D)

omit [Fintype V] [DecidableEq V] in
theorem del_iff (r : V → V → Prop) (S D : Finset V) (a b : V) :
    del r S D a b ↔ r a b ∧ ¬ (a ∈ S ∧ b ∈ D) := Iff.rfl

/-- The one-step improvement: for `T ⊊ E := F S \ S` there is a nonempty `Q ⊆ E \ T` with
`g (T ∪ Q) + 1 ≤ g T + |Q|`, where `g T = |F T \ (I ∪ T)|` and `I := F S ∩ S`. -/
theorem step (r : V → V → Prop) (hr : IsOriented r)
    (hbad : ∀ v, ¬ GoodVertex r v)
    (hmin_arcs : ∀ r' : V → V → Prop, (∀ a b, r' a b → r a b) → (∃ a b, r a b ∧ ¬ r' a b) →
      ∃ v, GoodVertex r' v)
    (S T : Finset V) (hT : T ⊆ fwd r S \ S) (hTne : T ≠ fwd r S \ S) :
    ∃ Q ⊆ (fwd r S \ S) \ T, Q.Nonempty ∧
      (fwd r (T ∪ Q) \ ((fwd r S ∩ S) ∪ (T ∪ Q))).card + 1 ≤
        (fwd r T \ ((fwd r S ∩ S) ∪ T)).card + Q.card := by
  set E := fwd r S \ S with hE
  set I := fwd r S ∩ S with hI
  set D := E \ T with hD
  have hDne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hTne
    exact Finset.Subset.antisymm hT (Finset.sdiff_eq_empty_iff_subset.1 h)
  have hmemD : ∀ w, w ∈ D ↔ w ∈ fwd r S ∧ w ∉ S ∧ w ∉ T := by
    intro w
    simp only [hD, hE, Finset.mem_sdiff]
    tauto
  have hmemI : ∀ w, w ∈ I ↔ w ∈ fwd r S ∧ w ∈ S := fun w => Finset.mem_inter
  have hsub : ∀ a b, del r S D a b → r a b := fun a b h => h.1
  have hmiss : ∃ a b, r a b ∧ ¬ del r S D a b := by
    obtain ⟨w, hw⟩ := hDne
    have hwF : w ∈ fwd r S := ((hmemD w).1 hw).1
    obtain ⟨x, hxS, hxw⟩ := (mem_fwd r S w).1 hwF
    exact ⟨x, w, hxw, fun h => h.2 ⟨hxS, hw⟩⟩
  obtain ⟨v, hv⟩ := hmin_arcs (del r S D) hsub hmiss
  -- `v ∈ S`
  have hvS : v ∈ S := by
    by_contra hvS
    apply hbad v
    refine good_of_sub_eq r (del r S D) hsub v ?_ hv
    intro w
    exact ⟨fun h => ⟨h, fun h' => hvS h'.1⟩, fun h => h.1⟩
  set Q := firstNeighbors r v ∩ D with hQ
  have hmemQ : ∀ w, w ∈ Q ↔ r v w ∧ w ∈ D := by
    intro w
    rw [hQ, Finset.mem_inter, mem_firstNeighbors]
  have hQne : Q.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hQe
    apply hbad v
    refine good_of_sub_eq r (del r S D) hsub v ?_ hv
    intro w
    refine ⟨fun h => ⟨h, fun h' => ?_⟩, fun h => h.1⟩
    have : w ∈ Q := (hmemQ w).2 ⟨h, h'.2⟩
    rw [hQe] at this
    exact Finset.notMem_empty w this
  have hQD : Q ⊆ D := Finset.inter_subset_right
  have hQN1 : Q ⊆ firstNeighbors r v := Finset.inter_subset_left
  -- (F1): the first neighbourhood of `v` in the pruned relation
  have hN1 : firstNeighbors (del r S D) v = firstNeighbors r v \ Q := by
    ext w
    rw [Finset.mem_sdiff, mem_firstNeighbors, mem_firstNeighbors, hmemQ, del_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ⟨hvS, h.2⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ⟨h1, h.2⟩⟩
  -- (4): two-step reach in the pruned relation
  have h4 : ∀ u w, del r S D v u → del r S D u w → w ∈ I ∪ T ∪ fwd r T := by
    intro u w hvu huw
    have huF : u ∈ fwd r S := (mem_fwd r S u).2 ⟨v, hvS, hvu.1⟩
    have huD : u ∉ D := fun h => hvu.2 ⟨hvS, h⟩
    simp only [Finset.mem_union]
    by_cases huS : u ∈ S
    · have hwF : w ∈ fwd r S := (mem_fwd r S w).2 ⟨u, huS, huw.1⟩
      have hwD : w ∉ D := fun h => huw.2 ⟨huS, h⟩
      by_cases hwS : w ∈ S
      · exact Or.inl (Or.inl ((hmemI w).2 ⟨hwF, hwS⟩))
      · left; right
        by_contra hwT
        exact hwD ((hmemD w).2 ⟨hwF, hwS, hwT⟩)
    · have huT : u ∈ T := by
        by_contra huT
        exact huD ((hmemD u).2 ⟨huF, huS, huT⟩)
      exact Or.inr ((mem_fwd r T w).2 ⟨u, huT, huw.1⟩)
  -- `N1 v ⊆ I ∪ T ∪ Q`
  have hN1sub : ∀ w, r v w → w ∈ I ∨ w ∈ T ∨ w ∈ Q := by
    intro w hw
    have hwF : w ∈ fwd r S := (mem_fwd r S w).2 ⟨v, hvS, hw⟩
    by_cases hwS : w ∈ S
    · exact Or.inl ((hmemI w).2 ⟨hwF, hwS⟩)
    · by_cases hwT : w ∈ T
      · exact Or.inr (Or.inl hwT)
      · exact Or.inr (Or.inr ((hmemQ w).2 ⟨hw, (hmemD w).2 ⟨hwF, hwS, hwT⟩⟩))
  set C := fwd r Q \ (I ∪ T ∪ Q ∪ fwd r T) with hC
  have hmemC : ∀ w, w ∈ C ↔ w ∈ fwd r Q ∧ w ∉ I ∧ w ∉ T ∧ w ∉ Q ∧ w ∉ fwd r T := by
    intro w
    simp only [hC, Finset.mem_sdiff, Finset.mem_union]
    tauto
  -- (C1): `C ⊆ N2 v`
  have hC1 : C ⊆ secondNeighbors r v := by
    intro w hw
    obtain ⟨hwFQ, hwI, hwT, hwQ, hwFT⟩ := (hmemC w).1 hw
    obtain ⟨q, hqQ, hqw⟩ := (mem_fwd r Q w).1 hwFQ
    have hvq : r v q := ((hmemQ q).1 hqQ).1
    rw [mem_secondNeighbors]
    refine ⟨?_, ?_, q, hvq, hqw⟩
    · rintro rfl
      exact hr.asymmetric hvq hqw
    · intro hvw
      rcases hN1sub w hvw with h | h | h
      · exact hwI h
      · exact hwT h
      · exact hwQ h
  -- (C2): `C` is disjoint from the pruned second neighbourhood
  have hC2 : Disjoint C (secondNeighbors (del r S D) v) := by
    rw [Finset.disjoint_left]
    intro w hwC hw2
    obtain ⟨hwFQ, hwI, hwT, hwQ, hwFT⟩ := (hmemC w).1 hwC
    obtain ⟨_, _, u, hvu, huw⟩ := (mem_secondNeighbors (del r S D) v w).1 hw2
    have := h4 u w hvu huw
    simp only [Finset.mem_union] at this
    rcases this with (h | h) | h
    · exact hwI h
    · exact hwT h
    · exact hwFT h
  -- (G): gains of the pruned second neighbourhood lie in `Q ∩ F T`
  have hG : secondNeighbors (del r S D) v ⊆ (secondNeighbors r v \ C) ∪ (Q ∩ fwd r T) := by
    intro w hw
    have hwC : w ∉ C := fun h => Finset.disjoint_left.1 hC2 h hw
    obtain ⟨hne, hnr, u, hvu, huw⟩ := (mem_secondNeighbors (del r S D) v w).1 hw
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    by_cases hw2 : w ∈ secondNeighbors r v
    · exact Or.inl ⟨hw2, hwC⟩
    · right
      have hvw : r v w := by
        by_contra hvw
        exact hw2 ((mem_secondNeighbors r v w).2 ⟨hne, hvw, u, hvu.1, huw.1⟩)
      have hwD : w ∈ D := by
        by_contra hwD
        exact hnr ⟨hvw, fun h => hwD h.2⟩
      have hwQ : w ∈ Q := (hmemQ w).2 ⟨hvw, hwD⟩
      refine ⟨hwQ, ?_⟩
      have := h4 u w hvu huw
      simp only [Finset.mem_union] at this
      obtain ⟨hwF, hwS, hwT⟩ := (hmemD w).1 hwD
      rcases this with (h | h) | h
      · exact absurd ((hmemI w).1 h).2 hwS
      · exact absurd h hwT
      · exact h
  -- counting
  have hgood : (firstNeighbors (del r S D) v).card ≤ (secondNeighbors (del r S D) v).card := hv
  have hbadv : (secondNeighbors r v).card < (firstNeighbors r v).card :=
    Nat.lt_of_not_le (hbad v)
  have k1 : (firstNeighbors r v \ Q).card + Q.card = (firstNeighbors r v).card :=
    Finset.card_sdiff_add_card_eq_card hQN1
  have k2 : (secondNeighbors r v \ C).card + C.card = (secondNeighbors r v).card :=
    Finset.card_sdiff_add_card_eq_card hC1
  have k3 : (secondNeighbors (del r S D) v).card ≤
      (secondNeighbors r v \ C).card + (Q ∩ fwd r T).card :=
    le_trans (Finset.card_le_card hG) (Finset.card_union_le _ _)
  rw [hN1] at hgood
  have key : C.card + 1 ≤ Q.card + (Q ∩ fwd r T).card := by omega
  -- (X): exact change of `g`
  have hX : fwd r (T ∪ Q) \ (I ∪ (T ∪ Q)) = ((fwd r T \ (I ∪ T)) \ Q) ∪ C := by
    ext w
    rw [fwd_union]
    simp only [Finset.mem_sdiff, Finset.mem_union, hmemC]
    tauto
  have hdisj : Disjoint ((fwd r T \ (I ∪ T)) \ Q) C := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    exact ((hmemC w).1 h2).2.2.2.2 (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 h1).1).1
  have k4 : (fwd r (T ∪ Q) \ (I ∪ (T ∪ Q))).card = ((fwd r T \ (I ∪ T)) \ Q).card + C.card := by
    rw [hX, Finset.card_union_of_disjoint hdisj]
  have k5 : ((fwd r T \ (I ∪ T)) \ Q).card + ((fwd r T \ (I ∪ T)) ∩ Q).card
      = (fwd r T \ (I ∪ T)).card := Finset.card_sdiff_add_card_inter _ _
  have k6 : (fwd r T \ (I ∪ T)) ∩ Q = Q ∩ fwd r T := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨hwF, hwS, hwT⟩ := (hmemD w).1 (hQD h1)
      exact ⟨⟨h2, fun h => h.elim (fun h' => hwS ((hmemI w).1 h').2) hwT⟩, h1⟩
  rw [k6] at k5
  refine ⟨Q, hQD, hQne, ?_⟩
  omega

/-- Iterating the step: for every `T ⊊ E`, `g E + 1 ≤ g T + |E \ T|`. -/
theorem induct (r : V → V → Prop) (hr : IsOriented r)
    (hbad : ∀ v, ¬ GoodVertex r v)
    (hmin_arcs : ∀ r' : V → V → Prop, (∀ a b, r' a b → r a b) → (∃ a b, r a b ∧ ¬ r' a b) →
      ∃ v, GoodVertex r' v)
    (S : Finset V) :
    ∀ n : ℕ, ∀ T : Finset V, T ⊆ fwd r S \ S → T ≠ fwd r S \ S →
      ((fwd r S \ S) \ T).card = n →
      (fwd r (fwd r S \ S) \ ((fwd r S ∩ S) ∪ (fwd r S \ S))).card + 1 ≤
        (fwd r T \ ((fwd r S ∩ S) ∪ T)).card + ((fwd r S \ S) \ T).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hT hTne hn
  obtain ⟨Q, hQ, hQne, hstep⟩ := step r hr hbad hmin_arcs S T hT hTne
  have hTQ : T ∪ Q ⊆ fwd r S \ S :=
    Finset.union_subset hT (subset_trans hQ Finset.sdiff_subset)
  have hsplit : (fwd r S \ S) \ (T ∪ Q) = ((fwd r S \ S) \ T) \ Q := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hcardQ : ((fwd r S \ S) \ (T ∪ Q)).card + Q.card = ((fwd r S \ S) \ T).card := by
    rw [hsplit]
    exact Finset.card_sdiff_add_card_eq_card hQ
  have hQpos : 0 < Q.card := Finset.card_pos.2 hQne
  by_cases heq : T ∪ Q = fwd r S \ S
  · rw [heq] at hstep
    have := Finset.card_le_card hQ
    omega
  · have hlt : ((fwd r S \ S) \ (T ∪ Q)).card < n := by omega
    have := ih _ hlt (T ∪ Q) hTQ heq rfl
    omega

/-- Part (2): the subset deficit. -/
theorem subsetDeficit (r : V → V → Prop) (hr : IsOriented r)
    (hbad : ∀ v, ¬ GoodVertex r v)
    (hmin_arcs : ∀ r' : V → V → Prop, (∀ a b, r' a b → r a b) → (∃ a b, r a b ∧ ¬ r' a b) →
      ∃ v, GoodVertex r' v)
    (hmin_order : ∀ W : Finset V, W.Nonempty → W ≠ univ →
      ∃ v : W, GoodVertex (fun a b : W => r a b) v) : SubsetDeficit r := by
  intro S hS hSu
  have hEne : fwd r S \ S ≠ ∅ := by
    intro hEe
    have hFS : fwd r S ⊆ S := Finset.sdiff_eq_empty_iff_subset.1 hEe
    obtain ⟨⟨u, hu⟩, hgu⟩ := hmin_order S hS hSu
    apply hbad u
    exact good_of_restrict r S u hu (fun w hw => hFS ((mem_fwd r S w).2 ⟨u, hu, hw⟩)) hgu
  have hind := induct r hr hbad hmin_arcs S _ ∅ (Finset.empty_subset _) (Ne.symm hEne) rfl
  rw [fwd_empty, Finset.empty_sdiff, Finset.card_empty, Finset.sdiff_empty] at hind
  have hset : fwd r (fwd r S) \ fwd r S = fwd r (fwd r S \ S) \ ((fwd r S ∩ S) ∪ (fwd r S \ S)) := by
    have hsplit : fwd r S = (fwd r S ∩ S) ∪ (fwd r S \ S) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hFI : fwd r (fwd r S ∩ S) ⊆ (fwd r S ∩ S) ∪ (fwd r S \ S) := by
      rw [← hsplit]
      exact fwd_mono r Finset.inter_subset_right
    ext w
    conv_lhs => rw [hsplit, fwd_union]
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · have h3 := hFI h1
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at h3
        exact absurd h3 h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  rw [hset]
  omega

end OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_lemma_2_2

open OAI.SeymourSecondNeighborhood in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (r : V → V → Prop)
    (hr : IsOriented r)
    (hbad : ∀ v, ¬ GoodVertex r v)
    (hmin_arcs : ∀ r' : V → V → Prop, (∀ a b, r' a b → r a b) → (∃ a b, r a b ∧ ¬ r' a b) →
      ∃ v, GoodVertex r' v)
    (hmin_order : ∀ W : Finset V, W.Nonempty → W ≠ univ →
      ∃ v : W, GoodVertex (fun a b : W => r a b) v) :
    PosIndeg r ∧ SubsetDeficit r :=
  ⟨OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_lemma_2_2.posIndeg
      r hr hbad hmin_order,
   OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_lemma_2_2.subsetDeficit
      r hr hbad hmin_arcs hmin_order⟩
