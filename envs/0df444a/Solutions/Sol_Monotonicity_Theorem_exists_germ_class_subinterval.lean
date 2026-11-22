-- Prove2me | solution 1 for Monotonicity_Theorem.exists_germ_class_subinterval
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T07:10:05.745513+00:00
-- url     : https://prove2.me/submissions/f5a3daef-f785-417c-9f9b-2e22ee9c6907

import Definitions.Def_Monotonicity_Theorem_Extremal_Germs

set_option autoImplicit false

namespace Monotonicity_Theorem

section Toolkit

variable {R : Type}

lemma power1_ext {a b : Power R 1} (h : a 0 = b 0) : a = b := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  exact h

lemma isFinite1_or {R : Type} {F₁ F₂ : Set (Power R 1)}
    (h₁ : IsFinite1 F₁) (h₂ : IsFinite1 F₂) : IsFinite1 (fun x => F₁ x ∨ F₂ x) := by
  obtain ⟨L₁, hL₁⟩ := h₁
  obtain ⟨L₂, hL₂⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_⟩
  intro x
  constructor
  · rintro (h | h)
    · exact List.mem_append.2 (Or.inl ((hL₁ x).1 h))
    · exact List.mem_append.2 (Or.inr ((hL₂ x).1 h))
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl ((hL₁ x).2 h)
    · exact Or.inr ((hL₂ x).2 h)

/-- The reindexing map sending `0` to `i` and `1` to `j`. -/
def pair2 {n : Nat} (i j : Fin n) : Fin 2 → Fin n := fun k => if k = 0 then i else j

lemma defin_lt {n : Nat} {D : DenseLinearOrderNoEndpoints R} (M : OMinimalStructure D)
    (i j : Fin n) : M.S n (fun t : Power R n => D.lt (t i) (t j)) :=
  M.reindex_mem (pair2 i j) M.lt_mem

lemma defin_at {n : Nat} {D : DenseLinearOrderNoEndpoints R} (M : OMinimalStructure D)
    (i : Fin n) {A : Set (Power R 1)} (hA : M.S 1 A) :
    M.S n (fun t : Power R n => A (fun _ => t i)) :=
  M.reindex_mem (fun _ : Fin 1 => i) hA

lemma defin_graph {n : Nat} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (i j : Fin n) :
    M.S n (fun t : Power R n =>
      ∃ h : I (fun _ => t i),
        (fun _ => t j : Power R 1) = (f.toFun (Subtype.mk (fun _ => t i) h)).1) := by
  have h := M.reindex_mem (pair2 i j) f.graph_mem
  have hset : (fun t : Power R n =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun k : Fin 2 => t (pair2 i j k)))
      = (fun t : Power R n => ∃ h : I (fun _ => t i),
        (fun _ => t j : Power R 1) = (f.toFun (Subtype.mk (fun _ => t i) h)).1) := by
    funext t
    have hl : Power.left (n := 1) (m := 1) (fun k : Fin 2 => t (pair2 i j k)) = (fun _ : Fin 1 => t i) := by
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      rw [ha]
      rfl
    have hr : Power.right (n := 1) (m := 1) (fun k : Fin 2 => t (pair2 i j k)) = (fun _ : Fin 1 => t j) := by
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      rw [ha]
      rfl
    show (∃ hx : I (Power.left (n := 1) (m := 1) (fun k : Fin 2 => t (pair2 i j k))),
        Power.right (n := 1) (m := 1) (fun k : Fin 2 => t (pair2 i j k))
          = (f.toFun (Subtype.mk (Power.left (n := 1) (m := 1) (fun k : Fin 2 => t (pair2 i j k))) hx)).1) = _
    rw [hl, hr]
  rw [hset] at h
  exact h

lemma exists_power3 {P : R → R → R → Prop} :
    (∃ y : Power R 3, P (y 0) (y 1) (y 2)) ↔ ∃ a b c : R, P a b c := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y 0, y 1, y 2, h⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨fun k => if k.val = 0 then a else if k.val = 1 then b else c, h⟩

/-- The point of the line with coordinate `t`. -/
def pt (t : R) : Power R 1 := fun _ => t

@[simp] lemma pt_apply (t : R) (i : Fin 1) : pt t i = t := rfl

lemma const_coord (x : Power R 1) : (fun _ : Fin 1 => x 0) = x := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]

lemma pt_coord (x : Power R 1) : pt (x 0) = x := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  rfl

/-- Inside any nonempty open interval one can find a subinterval avoiding a given finite
list of points. -/
lemma exists_subinterval_avoiding_list (D : DenseLinearOrderNoEndpoints R) :
    ∀ (L : List R) (u v : R), D.lt u v →
      ∃ u₁ v₁ : R, D.lt u₁ v₁ ∧
        (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x →
          openInterval D (Endpoint.finite u) (Endpoint.finite v) x) ∧
        (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x →
          x 0 ∉ L) := by
  intro L
  induction L with
  | nil =>
      intro u v huv
      exact ⟨u, v, huv, fun _ hx => hx, fun _ _ h => absurd h (by simp)⟩
  | cons a L ih =>
      intro u v huv
      obtain ⟨u₁, v₁, huv₁, hsub, havoid⟩ := ih u v huv
      by_cases ha : D.lt u₁ a ∧ D.lt a v₁
      · refine ⟨u₁, a, ha.1, ?_, ?_⟩
        · intro x hx
          exact hsub x ⟨hx.1, D.trans hx.2 ha.2⟩
        · intro x hx hmem
          rcases List.mem_cons.1 hmem with h | h
          · have hlt : D.lt (x 0) a := hx.2
            rw [← h] at hlt
            exact D.irrefl _ hlt
          · exact havoid x ⟨hx.1, D.trans hx.2 ha.2⟩ h
      · refine ⟨u₁, v₁, huv₁, hsub, ?_⟩
        intro x hx hmem
        rcases List.mem_cons.1 hmem with h | h
        · exact ha ⟨by rw [← h]; exact hx.1, by rw [← h]; exact hx.2⟩
        · exact havoid x hx h

/-- A nonempty open interval is infinite. -/
lemma interval_infinite (D : DenseLinearOrderNoEndpoints R) {u v : R} (huv : D.lt u v) :
    ¬ IsFinite1 (openInterval D (Endpoint.finite u) (Endpoint.finite v)) := by
  rintro ⟨L, hL⟩
  obtain ⟨u₁, v₁, huv₁, hsub, havoid⟩ := exists_subinterval_avoiding_list D L u v huv
  obtain ⟨z, hz₁, hz₂⟩ := D.dense huv₁
  exact havoid (pt z) ⟨hz₁, hz₂⟩ ((hL (pt z)).1 (hsub (pt z) ⟨hz₁, hz₂⟩))

/-- An infinite definable subset of the line contains a nonempty open interval. -/
lemma infinite_contains_interval (D : DenseLinearOrderNoEndpoints R)
    {A : Set (Power R 1)} (hA : FiniteUnionOfPointsAndIntervals D A) (hinf : ¬ IsFinite1 A) :
    ∃ u v : R, D.lt u v ∧
      (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset A := by
  have key : IsFinite1 A ∨ ∃ u v : R, D.lt u v ∧
      (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset A := by
    clear hinf
    induction hA with
    | empty => exact Or.inl ⟨[], fun x => ⟨False.elim, fun h => absurd h (by simp)⟩⟩
    | point a => exact Or.inl ⟨[a], fun x => by simp [pointSet, Power.coord1]⟩
    | interval p q =>
        by_cases hne : ∃ x : Power R 1, openInterval D p q x
        · obtain ⟨x, hx⟩ := hne
          refine Or.inr ?_
          have hleft : ∃ u : R, Endpoint.lt D p (Endpoint.finite u) ∧ D.lt u (x 0) := by
            cases p with
            | negInf =>
                obtain ⟨u, hu⟩ := D.no_left_endpoint (x 0)
                exact ⟨u, trivial, hu⟩
            | finite a =>
                obtain ⟨u, hu1, hu2⟩ := D.dense (show D.lt a (x 0) from hx.1)
                exact ⟨u, hu1, hu2⟩
            | posInf => exact absurd hx.1 (by simp [Endpoint.lt])
          have hright : ∃ v : R, Endpoint.lt D (Endpoint.finite v) q ∧ D.lt (x 0) v := by
            cases q with
            | posInf =>
                obtain ⟨v, hv⟩ := D.no_right_endpoint (x 0)
                exact ⟨v, trivial, hv⟩
            | finite b =>
                obtain ⟨v, hv1, hv2⟩ := D.dense (show D.lt (x 0) b from hx.2)
                exact ⟨v, hv2, hv1⟩
            | negInf => exact absurd hx.2 (by simp [Endpoint.lt])
          obtain ⟨u, hpu, hux⟩ := hleft
          obtain ⟨v, hvq, hxv⟩ := hright
          refine ⟨u, v, D.trans hux hxv, ?_⟩
          intro y hy
          refine ⟨?_, ?_⟩
          · cases p with
            | negInf => trivial
            | posInf => exact absurd hx.1 (by simp [Endpoint.lt])
            | finite a => exact D.trans hpu hy.1
          · cases q with
            | posInf => trivial
            | negInf => exact absurd hx.2 (by simp [Endpoint.lt])
            | finite b => exact D.trans hy.2 hvq
        · refine Or.inl ⟨[], fun x => ⟨fun hx => absurd ⟨x, hx⟩ hne, fun h => absurd h (by simp)⟩⟩
    | union _ _ ihA ihB =>
        rcases ihA with hfa | ⟨u, v, huv, hsub⟩
        · rcases ihB with hfb | ⟨u, v, huv, hsub⟩
          · exact Or.inl (isFinite1_or hfa hfb)
          · exact Or.inr ⟨u, v, huv, fun x hx => Or.inr (hsub hx)⟩
        · exact Or.inr ⟨u, v, huv, fun x hx => Or.inl (hsub hx)⟩
  rcases key with h | h
  · exact absurd h hinf
  · exact h

/-- A subset of a finite subset of the line is finite. -/
lemma isFinite1_subset {S T : Set (Power R 1)} (hT : IsFinite1 T) (hST : ∀ x, S x → T x) :
    IsFinite1 S := by
  classical
  obtain ⟨L, hL⟩ := hT
  refine ⟨L.filter (fun a => decide (S (pt a))), ?_⟩
  intro x
  constructor
  · intro hx
    refine List.mem_filter.2 ⟨(hL x).1 (hST x hx), ?_⟩
    simp only [decide_eq_true_eq]
    have he : pt (Power.coord1 x) = x := pt_coord x
    rw [he]
    exact hx
  · intro hx
    have h2 := (List.mem_filter.1 hx).2
    simp only [decide_eq_true_eq] at h2
    have he : pt (Power.coord1 x) = x := pt_coord x
    rw [he] at h2
    exact h2

/-- Choose a point strictly between `x` and `min b y`. -/
lemma exists_between_lt3 (D : DenseLinearOrderNoEndpoints R) {x y b : R}
    (hxy : D.lt x y) (hxb : D.lt x b) :
    ∃ t : R, D.lt x t ∧ D.lt t y ∧ D.lt t b := by
  rcases D.trichotomy b y with h | h | h
  · obtain ⟨t, h1, h2⟩ := D.dense hxb
    exact ⟨t, h1, D.trans h2 h.1, h2⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hxb
    exact ⟨t, h1, h.1 ▸ h2, h2⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hxy
    exact ⟨t, h1, h2, D.trans h2 h.1⟩

/-- The germ of a definable subset of the line immediately to the right of a point is either
"everything" or "nothing". -/
lemma germ_right (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (hA : FiniteUnionOfPointsAndIntervals D A) (x : R) :
    (∃ w : R, D.lt x w ∧ ∀ y : R, D.lt x y → D.lt y w → A (pt y)) ∨
    (∃ w : R, D.lt x w ∧ ∀ y : R, D.lt x y → D.lt y w → ¬ A (pt y)) := by
  induction hA with
  | empty =>
      obtain ⟨w, hw⟩ := D.no_right_endpoint x
      exact Or.inr ⟨w, hw, fun _ _ _ h => h⟩
  | point a =>
      rcases D.trichotomy x a with h | h | h
      · refine Or.inr ⟨a, h.1, ?_⟩
        intro y _ hya hy
        have : y = a := hy
        rw [this] at hya
        exact D.irrefl _ hya
      · obtain ⟨w, hw⟩ := D.no_right_endpoint x
        refine Or.inr ⟨w, hw, ?_⟩
        intro y hxy _ hy
        have hya : y = a := hy
        rw [hya, ← h.1] at hxy
        exact D.irrefl _ hxy
      · obtain ⟨w, hw⟩ := D.no_right_endpoint x
        refine Or.inr ⟨w, hw, ?_⟩
        intro y hxy _ hy
        have hya : y = a := hy
        rw [hya] at hxy
        exact h.2.1 hxy
  | interval p q =>
      by_cases hq : Endpoint.lt D (Endpoint.finite x) q
      · -- `x` lies strictly below the right endpoint
        cases p with
        | posInf =>
            obtain ⟨w, hw⟩ := D.no_right_endpoint x
            exact Or.inr ⟨w, hw, fun _ _ _ hy => (by simpa [Endpoint.lt] using hy.1)⟩
        | negInf =>
            cases q with
            | posInf =>
                obtain ⟨w, hw⟩ := D.no_right_endpoint x
                exact Or.inl ⟨w, hw, fun y _ _ => ⟨trivial, trivial⟩⟩
            | negInf => exact absurd hq (by simp [Endpoint.lt])
            | finite b =>
                exact Or.inl ⟨b, hq, fun y _ hyb => ⟨trivial, hyb⟩⟩
        | finite a =>
            rcases D.trichotomy x a with h | h | h
            · refine Or.inr ⟨a, h.1, ?_⟩
              intro y _ hya hy
              exact D.irrefl a (D.trans hy.1 hya)
            · cases q with
              | posInf =>
                  obtain ⟨w, hw⟩ := D.no_right_endpoint x
                  refine Or.inl ⟨w, hw, ?_⟩
                  intro y hxy _
                  exact ⟨h.1 ▸ hxy, trivial⟩
              | negInf => exact absurd hq (by simp [Endpoint.lt])
              | finite b =>
                  refine Or.inl ⟨b, hq, ?_⟩
                  intro y hxy hyb
                  exact ⟨h.1 ▸ hxy, hyb⟩
            · cases q with
              | posInf =>
                  obtain ⟨w, hw⟩ := D.no_right_endpoint x
                  refine Or.inl ⟨w, hw, ?_⟩
                  intro y hxy _
                  exact ⟨D.trans h.1 hxy, trivial⟩
              | negInf => exact absurd hq (by simp [Endpoint.lt])
              | finite b =>
                  refine Or.inl ⟨b, hq, ?_⟩
                  intro y hxy hyb
                  exact ⟨D.trans h.1 hxy, hyb⟩
      · -- `x` is at or beyond the right endpoint
        obtain ⟨w, hw⟩ := D.no_right_endpoint x
        refine Or.inr ⟨w, hw, ?_⟩
        intro y hxy _ hy
        cases q with
        | posInf => exact hq trivial
        | negInf => exact (by simpa [Endpoint.lt] using hy.2)
        | finite b =>
            have hyb : D.lt y b := hy.2
            rcases D.trichotomy x b with h | h | h
            · exact hq h.1
            · exact hq (by rw [h.1] at hxy ⊢; exact D.trans hxy hyb)
            · exact h.2.1 (D.trans hxy hyb)
  | union _ _ ihA ihB =>
      rcases ihA with ⟨w₁, hw₁, hall₁⟩ | ⟨w₁, hw₁, hnone₁⟩
      · exact Or.inl ⟨w₁, hw₁, fun y h1 h2 => Or.inl (hall₁ y h1 h2)⟩
      · rcases ihB with ⟨w₂, hw₂, hall₂⟩ | ⟨w₂, hw₂, hnone₂⟩
        · exact Or.inl ⟨w₂, hw₂, fun y h1 h2 => Or.inr (hall₂ y h1 h2)⟩
        · rcases D.trichotomy w₁ w₂ with h | h | h
          · exact Or.inr ⟨w₁, hw₁, fun y h1 h2 hy =>
              hy.elim (hnone₁ y h1 h2) (hnone₂ y h1 (D.trans h2 h.1))⟩
          · exact Or.inr ⟨w₁, hw₁, fun y h1 h2 hy =>
              hy.elim (hnone₁ y h1 h2) (hnone₂ y h1 (h.1 ▸ h2))⟩
          · exact Or.inr ⟨w₂, hw₂, fun y h1 h2 hy =>
              hy.elim (hnone₁ y h1 (D.trans h2 h.1)) (hnone₂ y h1 h2)⟩

/-- The germ of a definable subset of the line immediately to the left of a point is either
"everything" or "nothing". -/
lemma germ_left (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (hA : FiniteUnionOfPointsAndIntervals D A) (x : R) :
    (∃ w : R, D.lt w x ∧ ∀ y : R, D.lt w y → D.lt y x → A (pt y)) ∨
    (∃ w : R, D.lt w x ∧ ∀ y : R, D.lt w y → D.lt y x → ¬ A (pt y)) := by
  induction hA with
  | empty =>
      obtain ⟨w, hw⟩ := D.no_left_endpoint x
      exact Or.inr ⟨w, hw, fun _ _ _ h => h⟩
  | point a =>
      rcases D.trichotomy a x with h | h | h
      · refine Or.inr ⟨a, h.1, ?_⟩
        intro y hay _ hy
        have : y = a := hy
        rw [this] at hay
        exact D.irrefl _ hay
      · obtain ⟨w, hw⟩ := D.no_left_endpoint x
        refine Or.inr ⟨w, hw, ?_⟩
        intro y _ hyx hy
        have hya : y = a := hy
        rw [hya, h.1] at hyx
        exact D.irrefl _ hyx
      · obtain ⟨w, hw⟩ := D.no_left_endpoint x
        refine Or.inr ⟨w, hw, ?_⟩
        intro y _ hyx hy
        have hya : y = a := hy
        rw [hya] at hyx
        exact h.2.1 hyx
  | interval p q =>
      by_cases hp : Endpoint.lt D p (Endpoint.finite x)
      · cases q with
        | negInf =>
            obtain ⟨w, hw⟩ := D.no_left_endpoint x
            exact Or.inr ⟨w, hw, fun _ _ _ hy => (by simpa [Endpoint.lt] using hy.2)⟩
        | posInf =>
            cases p with
            | negInf =>
                obtain ⟨w, hw⟩ := D.no_left_endpoint x
                exact Or.inl ⟨w, hw, fun y _ _ => ⟨trivial, trivial⟩⟩
            | posInf => exact absurd hp (by simp [Endpoint.lt])
            | finite a =>
                exact Or.inl ⟨a, hp, fun y hay _ => ⟨hay, trivial⟩⟩
        | finite b =>
            rcases D.trichotomy b x with h | h | h
            · refine Or.inr ⟨b, h.1, ?_⟩
              intro y hby _ hy
              exact D.irrefl b (D.trans hby hy.2)
            · cases p with
              | negInf =>
                  obtain ⟨w, hw⟩ := D.no_left_endpoint x
                  refine Or.inl ⟨w, hw, ?_⟩
                  intro y _ hyx
                  exact ⟨trivial, h.1 ▸ hyx⟩
              | posInf => exact absurd hp (by simp [Endpoint.lt])
              | finite a =>
                  refine Or.inl ⟨a, hp, ?_⟩
                  intro y hay hyx
                  exact ⟨hay, h.1 ▸ hyx⟩
            · cases p with
              | negInf =>
                  obtain ⟨w, hw⟩ := D.no_left_endpoint x
                  refine Or.inl ⟨w, hw, ?_⟩
                  intro y _ hyx
                  exact ⟨trivial, D.trans hyx h.1⟩
              | posInf => exact absurd hp (by simp [Endpoint.lt])
              | finite a =>
                  refine Or.inl ⟨a, hp, ?_⟩
                  intro y hay hyx
                  exact ⟨hay, D.trans hyx h.1⟩
      · obtain ⟨w, hw⟩ := D.no_left_endpoint x
        refine Or.inr ⟨w, hw, ?_⟩
        intro y _ hyx hy
        cases p with
        | negInf => exact hp trivial
        | posInf => exact (by simpa [Endpoint.lt] using hy.1)
        | finite a =>
            have hay : D.lt a y := hy.1
            exact hp (D.trans hay hyx)
  | union _ _ ihA ihB =>
      rcases ihA with ⟨w₁, hw₁, hall₁⟩ | ⟨w₁, hw₁, hnone₁⟩
      · exact Or.inl ⟨w₁, hw₁, fun y h1 h2 => Or.inl (hall₁ y h1 h2)⟩
      · rcases ihB with ⟨w₂, hw₂, hall₂⟩ | ⟨w₂, hw₂, hnone₂⟩
        · exact Or.inl ⟨w₂, hw₂, fun y h1 h2 => Or.inr (hall₂ y h1 h2)⟩
        · rcases D.trichotomy w₁ w₂ with h | h | h
          · exact Or.inr ⟨w₂, hw₂, fun y h1 h2 hy =>
              hy.elim (hnone₁ y (D.trans h.1 h1) h2) (hnone₂ y h1 h2)⟩
          · exact Or.inr ⟨w₁, hw₁, fun y h1 h2 hy =>
              hy.elim (hnone₁ y h1 h2) (hnone₂ y (h.1 ▸ h1) h2)⟩
          · exact Or.inr ⟨w₁, hw₁, fun y h1 h2 hy =>
              hy.elim (hnone₁ y h1 h2) (hnone₂ y (D.trans h.1 h1) h2)⟩


end Toolkit

section Values

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

lemma fval_pt (f : DefinableFunction M I B) (x : Power R 1) (hx : I x)
    (h : I (pt (x 0))) : (f.toFun (Subtype.mk (pt (x 0)) h)).1 = (f.toFun (Subtype.mk x hx)).1 := by
  have he : (Subtype.mk (pt (x 0)) h : {w : Power R 1 // I w}) = Subtype.mk x hx :=
    Subtype.ext (pt_coord x)
  rw [he]

lemma graph_pt (f : DefinableFunction M I B) (z : Power R 1) (hz : I z) :
    ∃ h : I (fun _ : Fin 1 => z 0),
      (fun _ : Fin 1 => (f.toFun (Subtype.mk z hz)).1 0)
        = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) h)).1 := by
  have hz' : I (fun _ : Fin 1 => z 0) := by rw [const_coord z]; exact hz
  refine ⟨hz', ?_⟩
  have he : (Subtype.mk (fun _ : Fin 1 => z 0) hz' : {w : Power R 1 // I w}) = Subtype.mk z hz :=
    Subtype.ext (const_coord z)
  rw [he]
  exact power1_ext rfl


end Values




section Loci

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

lemma exists_power5 {P : R → R → R → R → R → Prop} :
    (∃ y : Power R 5, P (y 0) (y 1) (y 2) (y 3) (y 4)) ↔ ∃ a b c d e : R, P a b c d e := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y 0, y 1, y 2, y 3, y 4, h⟩
  · rintro ⟨a, b, c, d, e, h⟩
    exact ⟨fun k => if k.val = 0 then a else if k.val = 1 then b else if k.val = 2 then c
      else if k.val = 3 then d else e, h⟩

/-- Pairs `(x,w)` with `x < w` witnessing that `f` stays above `f x` on `(x,w)`. -/
def RightAbovePair (f : DefinableFunction M I B) : Set (Power R 2) :=
  fun p => D.lt (p 0) (p 1) ∧
    ¬ ∃ y cx cy : R,
      (∃ hx : I (fun _ : Fin 1 => p 0),
        (fun _ : Fin 1 => cx) = (f.toFun (Subtype.mk (fun _ : Fin 1 => p 0) hx)).1) ∧
      (∃ hy : I (fun _ : Fin 1 => y),
        (fun _ : Fin 1 => cy) = (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1) ∧
      D.lt (p 0) y ∧ D.lt y (p 1) ∧ ¬ D.lt cx cy

/-- Pairs `(x,w)` with `w < x` witnessing that `f` stays below `f x` on `(w,x)`. -/
def LeftBelowPair (f : DefinableFunction M I B) : Set (Power R 2) :=
  fun p => D.lt (p 1) (p 0) ∧
    ¬ ∃ y cx cy : R,
      (∃ hx : I (fun _ : Fin 1 => p 0),
        (fun _ : Fin 1 => cx) = (f.toFun (Subtype.mk (fun _ : Fin 1 => p 0) hx)).1) ∧
      (∃ hy : I (fun _ : Fin 1 => y),
        (fun _ : Fin 1 => cy) = (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1) ∧
      D.lt y (p 0) ∧ D.lt (p 1) y ∧ ¬ D.lt cy cx

/-- The locus of points near which, to the right, `f` stays above its value. -/
def RightAboveLocus (f : DefinableFunction M I B) : Set (Power R 1) :=
  fun x => ∃ w : Power R 1, RightAbovePair f (Power.append x w)

/-- The locus of points near which, to the left, `f` stays below its value. -/
def LeftBelowLocus (f : DefinableFunction M I B) : Set (Power R 1) :=
  fun x => ∃ w : Power R 1, LeftBelowPair f (Power.append x w)

lemma rightAbovePair_definable (f : DefinableFunction M I B) :
    M.S 2 (RightAbovePair f) := by
  have hBad : M.S 5 (fun t : Power R 5 =>
      (∃ h : I (fun _ => t 0),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      (∃ h : I (fun _ => t 2),
        (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
      D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ ¬ D.lt (t 3) (t 4)) :=
    M.inter_mem (defin_graph f 0 3) (M.inter_mem (defin_graph f 2 4)
      (M.inter_mem (defin_lt M 0 2) (M.inter_mem (defin_lt M 2 1)
        (M.compl_mem (defin_lt M 3 4)))))
  have hex := M.existsLast_mem (n := 2) (m := 3) hBad
  have hgood := M.inter_mem (defin_lt M (n := 2) 0 1) (M.compl_mem hex)
  have hset : setInter (fun p : Power R 2 => D.lt (p 0) (p 1))
      (setCompl (fun p : Power R 2 => ∃ y : Power R 3,
        (fun t : Power R 5 =>
          (∃ h : I (fun _ => t 0),
            (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
          (∃ h : I (fun _ => t 2),
            (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
          D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ ¬ D.lt (t 3) (t 4)) (Power.append p y)))
      = RightAbovePair f := by
    funext p
    apply propext
    constructor
    · rintro ⟨hlt, hno⟩
      refine ⟨hlt, ?_⟩
      intro hbad
      refine hno ?_
      obtain ⟨y, cx, cy, h1, h2, h3, h4, h5⟩ := hbad
      exact (exists_power3 (P := fun a b c =>
        (∃ h : I (fun _ : Fin 1 => p 0),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => p 0) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        D.lt (p 0) a ∧ D.lt a (p 1) ∧ ¬ D.lt b c)).2 ⟨y, cx, cy, h1, h2, h3, h4, h5⟩
    · rintro ⟨hlt, hno⟩
      refine ⟨hlt, ?_⟩
      intro hbad
      refine hno ?_
      exact (exists_power3 (P := fun a b c =>
        (∃ h : I (fun _ : Fin 1 => p 0),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => p 0) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        D.lt (p 0) a ∧ D.lt a (p 1) ∧ ¬ D.lt b c)).1 hbad
  rw [hset] at hgood
  exact hgood

lemma leftBelowPair_definable (f : DefinableFunction M I B) :
    M.S 2 (LeftBelowPair f) := by
  have hBad : M.S 5 (fun t : Power R 5 =>
      (∃ h : I (fun _ => t 0),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      (∃ h : I (fun _ => t 2),
        (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
      D.lt (t 2) (t 0) ∧ D.lt (t 1) (t 2) ∧ ¬ D.lt (t 4) (t 3)) :=
    M.inter_mem (defin_graph f 0 3) (M.inter_mem (defin_graph f 2 4)
      (M.inter_mem (defin_lt M 2 0) (M.inter_mem (defin_lt M 1 2)
        (M.compl_mem (defin_lt M 4 3)))))
  have hex := M.existsLast_mem (n := 2) (m := 3) hBad
  have hgood := M.inter_mem (defin_lt M (n := 2) 1 0) (M.compl_mem hex)
  have hset : setInter (fun p : Power R 2 => D.lt (p 1) (p 0))
      (setCompl (fun p : Power R 2 => ∃ y : Power R 3,
        (fun t : Power R 5 =>
          (∃ h : I (fun _ => t 0),
            (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
          (∃ h : I (fun _ => t 2),
            (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
          D.lt (t 2) (t 0) ∧ D.lt (t 1) (t 2) ∧ ¬ D.lt (t 4) (t 3)) (Power.append p y)))
      = LeftBelowPair f := by
    funext p
    apply propext
    constructor
    · rintro ⟨hlt, hno⟩
      refine ⟨hlt, ?_⟩
      intro hbad
      refine hno ?_
      obtain ⟨y, cx, cy, h1, h2, h3, h4, h5⟩ := hbad
      exact (exists_power3 (P := fun a b c =>
        (∃ h : I (fun _ : Fin 1 => p 0),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => p 0) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        D.lt a (p 0) ∧ D.lt (p 1) a ∧ ¬ D.lt c b)).2 ⟨y, cx, cy, h1, h2, h3, h4, h5⟩
    · rintro ⟨hlt, hno⟩
      refine ⟨hlt, ?_⟩
      intro hbad
      refine hno ?_
      exact (exists_power3 (P := fun a b c =>
        (∃ h : I (fun _ : Fin 1 => p 0),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => p 0) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        D.lt a (p 0) ∧ D.lt (p 1) a ∧ ¬ D.lt c b)).1 hbad
  rw [hset] at hgood
  exact hgood

lemma rightAboveLocus_definable (f : DefinableFunction M I B) :
    M.S 1 (RightAboveLocus f) :=
  M.existsLast_mem (n := 1) (m := 1) (rightAbovePair_definable f)

lemma leftBelowLocus_definable (f : DefinableFunction M I B) :
    M.S 1 (LeftBelowLocus f) :=
  M.existsLast_mem (n := 1) (m := 1) (leftBelowPair_definable f)

end Loci


section Dichotomy

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

/-- Singletons are definable, hence so is the condition "the `i`-th coordinate equals `a`". -/
lemma defin_const {n : Nat} (M : OMinimalStructure D) (i : Fin n) (a : R) :
    M.S n (fun t : Power R n => t i = a) :=
  defin_at M i ((M.ominimal (pointSet a)).2 (FiniteUnionOfPointsAndIntervals.point a))

/-- The set of points of the domain whose value exceeds the value of `f` at `x`. -/
def AboveOf (f : DefinableFunction M I B) (x : R) : Set (Power R 1) :=
  fun z => ∃ hz : I z, ∃ hx : I (fun _ : Fin 1 => x),
    D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)
      ((f.toFun (Subtype.mk z hz)).1 0)

lemma aboveOf_definable (f : DefinableFunction M I B) (x : R) : M.S 1 (AboveOf f x) := by
  have hT : M.S 4 (fun t : Power R 4 =>
      t 1 = x ∧
      (∃ h : I (fun _ => t 1),
        (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
      (∃ h : I (fun _ => t 0),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      D.lt (t 2) (t 3)) :=
    M.inter_mem (defin_const M 1 x)
      (M.inter_mem (defin_graph f 1 2) (M.inter_mem (defin_graph f 0 3) (defin_lt M 2 3)))
  have hex := M.existsLast_mem (n := 1) (m := 3) hT
  have hset : (fun z : Power R 1 => ∃ y : Power R 3,
      (fun t : Power R 4 =>
        t 1 = x ∧
        (∃ h : I (fun _ => t 1),
          (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
        (∃ h : I (fun _ => t 0),
          (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
        D.lt (t 2) (t 3)) (Power.append z y)) = AboveOf f x := by
    funext z
    apply propext
    constructor
    · intro hy
      obtain ⟨a, b, c, rfl, ⟨hx, hb⟩, ⟨hz0, hc⟩, hbc⟩ :=
        (exists_power3 (P := fun a b c =>
          a = x ∧
          (∃ h : I (fun _ : Fin 1 => a),
            (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
          (∃ h : I (fun _ : Fin 1 => z 0),
            (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) h)).1) ∧
          D.lt b c)).1 hy
      have hzI : I z := by rw [← const_coord z]; exact hz0
      refine ⟨hzI, hx, ?_⟩
      have hb0 : b = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) hx)).1 0 := congrFun hb 0
      have hc0 : c = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) hz0)).1 0 := congrFun hc 0
      have hzeq : (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) hz0)).1
          = (f.toFun (Subtype.mk z hzI)).1 := fval_pt f z hzI hz0
      rw [hb0, hc0, hzeq] at hbc
      exact hbc
    · rintro ⟨hz, hx, hlt⟩
      refine (exists_power3 (P := fun a b c =>
        a = x ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => z 0),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) h)).1) ∧
        D.lt b c)).2 ?_
      exact ⟨x, (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0,
        (f.toFun (Subtype.mk z hz)).1 0, rfl, ⟨hx, power1_ext rfl⟩, graph_pt f z hz, hlt⟩
  rw [hset] at hex
  exact hex

/-- The set of points of the domain whose value is below the value of `f` at `x`. -/
def BelowOf (f : DefinableFunction M I B) (x : R) : Set (Power R 1) :=
  fun z => ∃ hz : I z, ∃ hx : I (fun _ : Fin 1 => x),
    D.lt ((f.toFun (Subtype.mk z hz)).1 0)
      ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)

lemma belowOf_definable (f : DefinableFunction M I B) (x : R) : M.S 1 (BelowOf f x) := by
  have hT : M.S 4 (fun t : Power R 4 =>
      t 1 = x ∧
      (∃ h : I (fun _ => t 1),
        (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
      (∃ h : I (fun _ => t 0),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      D.lt (t 3) (t 2)) :=
    M.inter_mem (defin_const M 1 x)
      (M.inter_mem (defin_graph f 1 2) (M.inter_mem (defin_graph f 0 3) (defin_lt M 3 2)))
  have hex := M.existsLast_mem (n := 1) (m := 3) hT
  have hset : (fun z : Power R 1 => ∃ y : Power R 3,
      (fun t : Power R 4 =>
        t 1 = x ∧
        (∃ h : I (fun _ => t 1),
          (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
        (∃ h : I (fun _ => t 0),
          (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
        D.lt (t 3) (t 2)) (Power.append z y)) = BelowOf f x := by
    funext z
    apply propext
    constructor
    · intro hy
      obtain ⟨a, b, c, rfl, ⟨hx, hb⟩, ⟨hz0, hc⟩, hbc⟩ :=
        (exists_power3 (P := fun a b c =>
          a = x ∧
          (∃ h : I (fun _ : Fin 1 => a),
            (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
          (∃ h : I (fun _ : Fin 1 => z 0),
            (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) h)).1) ∧
          D.lt c b)).1 hy
      have hzI : I z := by rw [← const_coord z]; exact hz0
      refine ⟨hzI, hx, ?_⟩
      have hb0 : b = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) hx)).1 0 := congrFun hb 0
      have hc0 : c = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) hz0)).1 0 := congrFun hc 0
      have hzeq : (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) hz0)).1
          = (f.toFun (Subtype.mk z hzI)).1 := fval_pt f z hzI hz0
      rw [hb0, hc0, hzeq] at hbc
      exact hbc
    · rintro ⟨hz, hx, hlt⟩
      refine (exists_power3 (P := fun a b c =>
        a = x ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => z 0),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) h)).1) ∧
        D.lt c b)).2 ?_
      exact ⟨x, (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0,
        (f.toFun (Subtype.mk z hz)).1 0, rfl, ⟨hx, power1_ext rfl⟩, graph_pt f z hz, hlt⟩
  rw [hset] at hex
  exact hex

/-- A right window on which `f` stays above its value at `x` witnesses membership in
`RightAboveLocus`. -/
lemma rightAboveLocus_of (f : DefinableFunction M I B) {x w : R}
    (hx : I (fun _ : Fin 1 => x)) (hxw : D.lt x w)
    (hprop : ∀ y (hy : I (fun _ : Fin 1 => y)), D.lt x y → D.lt y w →
      D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0)) :
    RightAboveLocus f (fun _ : Fin 1 => x) := by
  refine ⟨fun _ => w, hxw, ?_⟩
  rintro ⟨y, cx, cy, ⟨hx', hex⟩, ⟨hy, hey⟩, h3, h4, h5⟩
  refine h5 ?_
  have hcx : cx = (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx')).1 0 := congrFun hex 0
  have hcy : cy = (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0 := congrFun hey 0
  rw [hcx, hcy]
  exact hprop y hy h3 h4

/-- Membership in `RightAboveLocus` gives a right window on which `f` stays above its value. -/
lemma rightAboveLocus_elim (f : DefinableFunction M I B) {x : R}
    (hx : I (fun _ : Fin 1 => x)) (h : RightAboveLocus f (fun _ : Fin 1 => x)) :
    ∃ w : R, D.lt x w ∧ ∀ y (hy : I (fun _ : Fin 1 => y)), D.lt x y → D.lt y w →
      D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0) := by
  obtain ⟨W, hlt, hno⟩ := h
  refine ⟨W 0, hlt, ?_⟩
  intro y hy h1 h2
  by_contra hcon
  exact hno ⟨y, (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0,
    (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0,
    ⟨hx, power1_ext rfl⟩, ⟨hy, power1_ext rfl⟩, h1, h2, hcon⟩

/-- A left window on which `f` stays below its value at `x` witnesses membership in
`LeftBelowLocus`. -/
lemma leftBelowLocus_of (f : DefinableFunction M I B) {x w : R}
    (hx : I (fun _ : Fin 1 => x)) (hwx : D.lt w x)
    (hprop : ∀ y (hy : I (fun _ : Fin 1 => y)), D.lt w y → D.lt y x →
      D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)) :
    LeftBelowLocus f (fun _ : Fin 1 => x) := by
  refine ⟨fun _ => w, hwx, ?_⟩
  rintro ⟨y, cx, cy, ⟨hx', hex⟩, ⟨hy, hey⟩, h3, h4, h5⟩
  refine h5 ?_
  have hcx : cx = (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx')).1 0 := congrFun hex 0
  have hcy : cy = (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0 := congrFun hey 0
  rw [hcx, hcy]
  exact hprop y hy h4 h3

/-- Membership in `LeftBelowLocus` gives a left window on which `f` stays below its value. -/
lemma leftBelowLocus_elim (f : DefinableFunction M I B) {x : R}
    (hx : I (fun _ : Fin 1 => x)) (h : LeftBelowLocus f (fun _ : Fin 1 => x)) :
    ∃ w : R, D.lt w x ∧ ∀ y (hy : I (fun _ : Fin 1 => y)), D.lt w y → D.lt y x →
      D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0) := by
  obtain ⟨W, hlt, hno⟩ := h
  refine ⟨W 0, hlt, ?_⟩
  intro y hy h1 h2
  by_contra hcon
  exact hno ⟨y, (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0,
    (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0,
    ⟨hx, power1_ext rfl⟩, ⟨hy, power1_ext rfl⟩, h2, h1, hcon⟩

section Cases

variable {u v : R}

/-- To the right of a point of an interval on which `f` is injective, either `f` stays above
its value at the point, or it stays below it. -/
lemma right_germ_cases (f : DefinableFunction M I B)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    {x : R} (hx : I (fun _ : Fin 1 => x))
    (hxuv : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ : Fin 1 => x)) :
    RightAboveLocus f (fun _ : Fin 1 => x) ∨
      ∃ w : R, D.lt x w ∧ ∀ y (hy : I (fun _ : Fin 1 => y)), D.lt x y → D.lt y w → D.lt y v →
        D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0)
          ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0) := by
  rcases germ_right D ((M.ominimal (AboveOf f x)).1 (aboveOf_definable f x)) x with
    ⟨w, hxw, hall⟩ | ⟨w, hxw, hnone⟩
  · refine Or.inl (rightAboveLocus_of f hx hxw ?_)
    intro y hy h1 h2
    obtain ⟨hy2, hx2, hlt⟩ := hall y h1 h2
    exact hlt
  · refine Or.inr ⟨w, hxw, ?_⟩
    intro y hy h1 h2 h3
    have hnot : ¬ D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0) :=
      fun hlt => hnone y h1 h2 ⟨hy, hx, hlt⟩
    have hyuv : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ : Fin 1 => y) :=
      ⟨D.trans hxuv.1 h1, h3⟩
    rcases D.trichotomy ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0) with hc | hc | hc
    · exact absurd hc.1 hnot
    · exfalso
      have heq : f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)
          = f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy) := Subtype.ext (power1_ext hc.1)
      have hxy : x = y := congrFun (hinj _ hx hxuv _ hy hyuv heq) 0
      rw [← hxy] at h1
      exact D.irrefl x h1
    · exact hc.1

/-- To the left of a point of an interval on which `f` is injective, either `f` stays below
its value at the point, or it stays above it. -/
lemma left_germ_cases (f : DefinableFunction M I B)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    {x : R} (hx : I (fun _ : Fin 1 => x))
    (hxuv : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ : Fin 1 => x)) :
    LeftBelowLocus f (fun _ : Fin 1 => x) ∨
      ∃ w : R, D.lt w x ∧ ∀ y (hy : I (fun _ : Fin 1 => y)), D.lt w y → D.lt y x → D.lt u y →
        D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)
          ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0) := by
  rcases germ_left D ((M.ominimal (BelowOf f x)).1 (belowOf_definable f x)) x with
    ⟨w, hwx, hall⟩ | ⟨w, hwx, hnone⟩
  · refine Or.inl (leftBelowLocus_of f hx hwx ?_)
    intro y hy h1 h2
    obtain ⟨hy2, hx2, hlt⟩ := hall y h1 h2
    exact hlt
  · refine Or.inr ⟨w, hwx, ?_⟩
    intro y hy h1 h2 h3
    have hnot : ¬ D.lt ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0) :=
      fun hlt => hnone y h1 h2 ⟨hy, hx, hlt⟩
    have hyuv : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ : Fin 1 => y) :=
      ⟨h3, D.trans h2 hxuv.2⟩
    rcases D.trichotomy ((f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0)
        ((f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy)).1 0) with hc | hc | hc
    · exact hc.1
    · exfalso
      have heq : f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)
          = f.toFun (Subtype.mk (fun _ : Fin 1 => y) hy) := Subtype.ext (power1_ext hc.1)
      have hxy : x = y := congrFun (hinj _ hx hxuv _ hy hyuv heq) 0
      rw [← hxy] at h2
      exact D.irrefl x h2
    · exact absurd hc.1 hnot

/-- Eta-conversion for values of `f`. -/
lemma fval_eta (f : DefinableFunction M I B) (x : Power R 1) (hx : I x)
    (h : I (fun _ : Fin 1 => x 0)) :
    (f.toFun (Subtype.mk (fun _ : Fin 1 => x 0) h)).1 = (f.toFun (Subtype.mk x hx)).1 :=
  fval_pt f x hx h

lemma mem_eta {x : Power R 1} (hx : I x) : I (fun _ : Fin 1 => x 0) := by
  rw [const_coord x]; exact hx

/-- A point of `RightAboveLocus` has a right window on which `f` stays above its value. -/
lemma right_above_window (f : DefinableFunction M I B) {x : Power R 1} (hx : I x)
    (h : RightAboveLocus f x) :
    ∃ w : R, D.lt (x 0) w ∧ ∀ y (hy : I y), D.lt (x 0) (y 0) → D.lt (y 0) w →
      D.lt ((f.toFun (Subtype.mk x hx)).1 0) ((f.toFun (Subtype.mk y hy)).1 0) := by
  have hx0 : I (fun _ : Fin 1 => x 0) := mem_eta hx
  have h' : RightAboveLocus f (fun _ : Fin 1 => x 0) := by rw [const_coord x]; exact h
  obtain ⟨w, hw, hprop⟩ := rightAboveLocus_elim f hx0 h'
  refine ⟨w, hw, ?_⟩
  intro y hy h1 h2
  have hy0 : I (fun _ : Fin 1 => y 0) := mem_eta hy
  have hthis := hprop (y 0) hy0 h1 h2
  rw [fval_eta f x hx hx0, fval_eta f y hy hy0] at hthis
  exact hthis

/-- A point of `LeftBelowLocus` has a left window on which `f` stays below its value. -/
lemma left_below_window (f : DefinableFunction M I B) {x : Power R 1} (hx : I x)
    (h : LeftBelowLocus f x) :
    ∃ w : R, D.lt w (x 0) ∧ ∀ y (hy : I y), D.lt w (y 0) → D.lt (y 0) (x 0) →
      D.lt ((f.toFun (Subtype.mk y hy)).1 0) ((f.toFun (Subtype.mk x hx)).1 0) := by
  have hx0 : I (fun _ : Fin 1 => x 0) := mem_eta hx
  have h' : LeftBelowLocus f (fun _ : Fin 1 => x 0) := by rw [const_coord x]; exact h
  obtain ⟨w, hw, hprop⟩ := leftBelowLocus_elim f hx0 h'
  refine ⟨w, hw, ?_⟩
  intro y hy h1 h2
  have hy0 : I (fun _ : Fin 1 => y 0) := mem_eta hy
  have hthis := hprop (y 0) hy0 h1 h2
  rw [fval_eta f x hx hx0, fval_eta f y hy hy0] at hthis
  exact hthis

/-- A point outside `RightAboveLocus` has a right window inside `(u,v)` on which `f` stays
below its value. -/
lemma right_below_window (f : DefinableFunction M I B)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    {x : Power R 1} (hx : I x)
    (hxuv : openInterval D (Endpoint.finite u) (Endpoint.finite v) x)
    (h : ¬ RightAboveLocus f x) :
    ∃ w : R, D.lt (x 0) w ∧ ∀ y (hy : I y), D.lt (x 0) (y 0) → D.lt (y 0) w → D.lt (y 0) v →
      D.lt ((f.toFun (Subtype.mk y hy)).1 0) ((f.toFun (Subtype.mk x hx)).1 0) := by
  have hx0 : I (fun _ : Fin 1 => x 0) := mem_eta hx
  have hxuv0 : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ : Fin 1 => x 0) := by
    rw [const_coord x]; exact hxuv
  rcases right_germ_cases f hinj hx0 hxuv0 with hRA | ⟨w, hw, hprop⟩
  · exact absurd (by rw [← const_coord x]; exact hRA) h
  · refine ⟨w, hw, ?_⟩
    intro y hy h1 h2 h3
    have hy0 : I (fun _ : Fin 1 => y 0) := mem_eta hy
    have hthis := hprop (y 0) hy0 h1 h2 h3
    rw [fval_eta f x hx hx0, fval_eta f y hy hy0] at hthis
    exact hthis

/-- A point outside `LeftBelowLocus` has a left window inside `(u,v)` on which `f` stays
above its value. -/
lemma left_above_window (f : DefinableFunction M I B)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    {x : Power R 1} (hx : I x)
    (hxuv : openInterval D (Endpoint.finite u) (Endpoint.finite v) x)
    (h : ¬ LeftBelowLocus f x) :
    ∃ w : R, D.lt w (x 0) ∧ ∀ y (hy : I y), D.lt w (y 0) → D.lt (y 0) (x 0) → D.lt u (y 0) →
      D.lt ((f.toFun (Subtype.mk x hx)).1 0) ((f.toFun (Subtype.mk y hy)).1 0) := by
  have hx0 : I (fun _ : Fin 1 => x 0) := mem_eta hx
  have hxuv0 : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ : Fin 1 => x 0) := by
    rw [const_coord x]; exact hxuv
  rcases left_germ_cases f hinj hx0 hxuv0 with hLB | ⟨w, hw, hprop⟩
  · exact absurd (by rw [← const_coord x]; exact hLB) h
  · refine ⟨w, hw, ?_⟩
    intro y hy h1 h2 h3
    have hy0 : I (fun _ : Fin 1 => y 0) := mem_eta hy
    have hthis := hprop (y 0) hy0 h1 h2 h3
    rw [fval_eta f x hx hx0, fval_eta f y hy hy0] at hthis
    exact hthis

end Cases

end Dichotomy





section Patterns

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}



/-- A germ pattern of `f` on `(u,v)` with prescribed comparisons on the two sides. -/
def UniformPattern (D : DenseLinearOrderNoEndpoints R) {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (u v : R)
    (L Rt : R → R → Prop) : Prop :=
  ∀ x (hxI : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
    ∃ c₁ c₂ : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) c₁ ∧
      openInterval D (Endpoint.finite u) (Endpoint.finite v) c₂ ∧
      Lt1 D c₁ x ∧ Lt1 D x c₂ ∧
      (∀ y (hyI : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        Lt1 D c₁ y → Lt1 D y x →
        L ((f.toFun (Subtype.mk y hyI)).1 0) ((f.toFun (Subtype.mk x hxI)).1 0)) ∧
      (∀ y (hyI : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        Lt1 D x y → Lt1 D y c₂ →
        Rt ((f.toFun (Subtype.mk x hxI)).1 0) ((f.toFun (Subtype.mk y hyI)).1 0))

/-- Choose a point strictly between `x` and both `y` and `b`, on the left. -/
lemma exists_between_gt3 (D : DenseLinearOrderNoEndpoints R) {x y b : R}
    (hyx : D.lt y x) (hbx : D.lt b x) :
    ∃ t : R, D.lt t x ∧ D.lt y t ∧ D.lt b t := by
  rcases D.trichotomy b y with h | h | h
  · obtain ⟨t, h1, h2⟩ := D.dense hyx
    exact ⟨t, h2, h1, D.trans h.1 h1⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hyx
    exact ⟨t, h2, h1, h.1 ▸ h1⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hbx
    exact ⟨t, h2, D.trans h.1 h1, h1⟩

/-- Pointwise one-sided windows, shrunk into the interval, give a uniform germ pattern. -/
lemma uniform_of_windows (f : DefinableFunction M I B) {u1 v1 : R} {L Rt : R → R → Prop}
    (hL : ∀ x (hx : I x), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      ∃ w : R, D.lt w (x 0) ∧ ∀ y (hy : I y),
        openInterval D (Endpoint.finite u1) (Endpoint.finite v1) y →
        D.lt w (y 0) → D.lt (y 0) (x 0) →
        L ((f.toFun (Subtype.mk y hy)).1 0) ((f.toFun (Subtype.mk x hx)).1 0))
    (hR : ∀ x (hx : I x), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      ∃ w : R, D.lt (x 0) w ∧ ∀ y (hy : I y),
        openInterval D (Endpoint.finite u1) (Endpoint.finite v1) y →
        D.lt (x 0) (y 0) → D.lt (y 0) w →
        Rt ((f.toFun (Subtype.mk x hx)).1 0) ((f.toFun (Subtype.mk y hy)).1 0)) :
    UniformPattern D f u1 v1 L Rt := by
  intro x hxI hxJ
  obtain ⟨wl, hwl, hLp⟩ := hL x hxI hxJ
  obtain ⟨wr, hwr, hRp⟩ := hR x hxI hxJ
  obtain ⟨c2, hxc2, hc2r, hc2v⟩ := exists_between_lt3 D hwr hxJ.2
  obtain ⟨c1, hc1x, hc1l, hc1u⟩ := exists_between_gt3 D hwl hxJ.1
  refine ⟨fun _ => c1, fun _ => c2, ⟨hc1u, D.trans hc1x hxJ.2⟩,
    ⟨D.trans hxJ.1 hxc2, hc2v⟩, hc1x, hxc2, ?_, ?_⟩
  · intro y hyI hyJ h1 h2
    exact hLp y hyI hyJ (D.trans hc1l h1) h2
  · intro y hyI hyJ h1 h2
    exact hRp y hyI hyJ h1 (D.trans h2 hc2r)

section Classes

variable {u v u1 v1 : R}

/-- On an interval of points that are in both loci, `f` has the below-above pattern. -/
lemma uniform_below_above_of_class (f : DefinableFunction M I B)
    (hRA : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      RightAboveLocus f x)
    (hLB : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      LeftBelowLocus f x) :
    UniformBelowAbove D f u1 v1 := by
  show UniformPattern D f u1 v1 (fun a b => D.lt a b) (fun a b => D.lt a b)
  refine uniform_of_windows f ?_ ?_
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := left_below_window f hx (hLB x hxJ)
    exact ⟨w, hw, fun y hy _ h1 h2 => hp y hy h1 h2⟩
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := right_above_window f hx (hRA x hxJ)
    exact ⟨w, hw, fun y hy _ h1 h2 => hp y hy h1 h2⟩

/-- On an interval of points in the right locus but not the left one, `f` has the above-above
pattern. -/
lemma uniform_above_above_of_class (f : DefinableFunction M I B)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    (hs1 : (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
      (openInterval D (Endpoint.finite u) (Endpoint.finite v)))
    (hRA : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      RightAboveLocus f x)
    (hLB : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      ¬ LeftBelowLocus f x) :
    UniformAboveAbove D f u1 v1 := by
  show UniformPattern D f u1 v1 (fun a b => D.lt b a) (fun a b => D.lt a b)
  refine uniform_of_windows f ?_ ?_
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := left_above_window f hinj hx (hs1 hxJ) (hLB x hxJ)
    exact ⟨w, hw, fun y hy hyJ h1 h2 => hp y hy h1 h2 (hs1 hyJ).1⟩
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := right_above_window f hx (hRA x hxJ)
    exact ⟨w, hw, fun y hy _ h1 h2 => hp y hy h1 h2⟩

/-- On an interval of points in the left locus but not the right one, `f` has the below-below
pattern. -/
lemma uniform_below_below_of_class (f : DefinableFunction M I B)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    (hs1 : (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
      (openInterval D (Endpoint.finite u) (Endpoint.finite v)))
    (hRA : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      ¬ RightAboveLocus f x)
    (hLB : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      LeftBelowLocus f x) :
    UniformBelowBelow D f u1 v1 := by
  show UniformPattern D f u1 v1 (fun a b => D.lt a b) (fun a b => D.lt b a)
  refine uniform_of_windows f ?_ ?_
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := left_below_window f hx (hLB x hxJ)
    exact ⟨w, hw, fun y hy _ h1 h2 => hp y hy h1 h2⟩
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := right_below_window f hinj hx (hs1 hxJ) (hRA x hxJ)
    exact ⟨w, hw, fun y hy hyJ h1 h2 => hp y hy h1 h2 (hs1 hyJ).2⟩

/-- On an interval of points in neither locus, `f` has the above-below pattern. -/
lemma uniform_above_below_of_class (f : DefinableFunction M I B)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    (hs1 : (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
      (openInterval D (Endpoint.finite u) (Endpoint.finite v)))
    (hRA : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      ¬ RightAboveLocus f x)
    (hLB : ∀ x, openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      ¬ LeftBelowLocus f x) :
    UniformAboveBelow D f u1 v1 := by
  show UniformPattern D f u1 v1 (fun a b => D.lt b a) (fun a b => D.lt b a)
  refine uniform_of_windows f ?_ ?_
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := left_above_window f hinj hx (hs1 hxJ) (hLB x hxJ)
    exact ⟨w, hw, fun y hy hyJ h1 h2 => hp y hy h1 h2 (hs1 hyJ).1⟩
  · intro x hx hxJ
    obtain ⟨w, hw, hp⟩ := right_below_window f hinj hx (hs1 hxJ) (hRA x hxJ)
    exact ⟨w, hw, fun y hy hyJ h1 h2 => hp y hy h1 h2 (hs1 hyJ).2⟩

end Classes

end Patterns

section Theorem

variable {R : Type}

/-- On a subinterval, the germ class of an injective definable function is constant. -/
theorem exists_germ_class_subinterval (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :
    ∃ u1 v1 : R, D.lt u1 v1 ∧
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) ∧
      (UniformBelowAbove D f u1 v1 ∨ UniformAboveBelow D f u1 v1 ∨
        UniformAboveAbove D f u1 v1 ∨ UniformBelowBelow D f u1 v1) := by
  classical
  have hJ : M.S 1 (openInterval D (Endpoint.finite u) (Endpoint.finite v)) :=
    (M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hRA := rightAboveLocus_definable f
  have hLB := leftBelowLocus_definable f
  have hC1 : M.S 1 (fun x : Power R 1 =>
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
        RightAboveLocus f x ∧ LeftBelowLocus f x) :=
    M.inter_mem hJ (M.inter_mem hRA hLB)
  have hC2 : M.S 1 (fun x : Power R 1 =>
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
        RightAboveLocus f x ∧ ¬ LeftBelowLocus f x) :=
    M.inter_mem hJ (M.inter_mem hRA (M.compl_mem hLB))
  have hC3 : M.S 1 (fun x : Power R 1 =>
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
        ¬ RightAboveLocus f x ∧ LeftBelowLocus f x) :=
    M.inter_mem hJ (M.inter_mem (M.compl_mem hRA) hLB)
  have hC4 : M.S 1 (fun x : Power R 1 =>
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
        ¬ RightAboveLocus f x ∧ ¬ LeftBelowLocus f x) :=
    M.inter_mem hJ (M.inter_mem (M.compl_mem hRA) (M.compl_mem hLB))
  by_cases hf1 : IsFinite1 (fun x : Power R 1 =>
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
        RightAboveLocus f x ∧ LeftBelowLocus f x)
  · by_cases hf2 : IsFinite1 (fun x : Power R 1 =>
        openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
          RightAboveLocus f x ∧ ¬ LeftBelowLocus f x)
    · by_cases hf3 : IsFinite1 (fun x : Power R 1 =>
          openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
            ¬ RightAboveLocus f x ∧ LeftBelowLocus f x)
      · by_cases hf4 : IsFinite1 (fun x : Power R 1 =>
            openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧
              ¬ RightAboveLocus f x ∧ ¬ LeftBelowLocus f x)
        · exfalso
          refine interval_infinite D huv
            (isFinite1_subset (isFinite1_or hf1 (isFinite1_or hf2 (isFinite1_or hf3 hf4))) ?_)
          intro x hx
          by_cases hA : RightAboveLocus f x <;> by_cases hB : LeftBelowLocus f x
          · exact Or.inl ⟨hx, hA, hB⟩
          · exact Or.inr (Or.inl ⟨hx, hA, hB⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨hx, hA, hB⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨hx, hA, hB⟩))
        · obtain ⟨u1, v1, h1, hsubC⟩ :=
            infinite_contains_interval D ((M.ominimal _).1 hC4) hf4
          refine ⟨u1, v1, h1, fun _ hx => (hsubC hx).1, Or.inr (Or.inl ?_)⟩
          exact uniform_above_below_of_class f hinj (fun _ hx => (hsubC hx).1)
            (fun x hx => (hsubC hx).2.1) (fun x hx => (hsubC hx).2.2)
      · obtain ⟨u1, v1, h1, hsubC⟩ :=
          infinite_contains_interval D ((M.ominimal _).1 hC3) hf3
        refine ⟨u1, v1, h1, fun _ hx => (hsubC hx).1, Or.inr (Or.inr (Or.inr ?_))⟩
        exact uniform_below_below_of_class f hinj (fun _ hx => (hsubC hx).1)
          (fun x hx => (hsubC hx).2.1) (fun x hx => (hsubC hx).2.2)
    · obtain ⟨u1, v1, h1, hsubC⟩ :=
        infinite_contains_interval D ((M.ominimal _).1 hC2) hf2
      refine ⟨u1, v1, h1, fun _ hx => (hsubC hx).1, Or.inr (Or.inr (Or.inl ?_))⟩
      exact uniform_above_above_of_class f hinj (fun _ hx => (hsubC hx).1)
        (fun x hx => (hsubC hx).2.1) (fun x hx => (hsubC hx).2.2)
  · obtain ⟨u1, v1, h1, hsubC⟩ :=
      infinite_contains_interval D ((M.ominimal _).1 hC1) hf1
    refine ⟨u1, v1, h1, fun _ hx => (hsubC hx).1, Or.inl ?_⟩
    exact uniform_below_above_of_class f (fun x hx => (hsubC hx).2.1)
      (fun x hx => (hsubC hx).2.2)

end Theorem



end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :
    ∃ u1 v1 : R, D.lt u1 v1 ∧
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) ∧
      (UniformBelowAbove D f u1 v1 ∨ UniformAboveBelow D f u1 v1 ∨
        UniformAboveAbove D f u1 v1 ∨ UniformBelowBelow D f u1 v1) :=
  Monotonicity_Theorem.exists_germ_class_subinterval D M f u v huv hsub hinj
