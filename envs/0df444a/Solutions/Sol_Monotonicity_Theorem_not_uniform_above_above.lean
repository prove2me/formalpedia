-- Prove2me | solution 1 for Monotonicity_Theorem.not_uniform_above_above
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T09:14:43.191802+00:00
-- url     : https://prove2.me/submissions/94664f6a-7ebb-4679-9147-a50519a8b4ce

import Definitions.Def_Monotonicity_Theorem_Extremal_Germs

set_option autoImplicit false

/-! ### Preimage -/


namespace Monotonicity_Theorem

variable {R : Type}

lemma power1_ext {a b : Power R 1} (h : a 0 = b 0) : a = b := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  exact h

/-- The preimage under a definable function of a definable subset of the codomain is definable. -/
theorem definable_preimage (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    {T : Set (Power R 1)} (hT : M.S 1 T) :
    M.S 1 (fun y : Power R 1 => ∃ hy : I y, T (f.toFun (Subtype.mk y hy)).1) := by
  have huniv : M.S 1 (setCompl (setEmpty : Set (Power R 1))) := M.compl_mem (M.empty_mem 1)
  have hP : M.S (1 + 1) (fun z : Power R (1 + 1) =>
      setCompl (setEmpty : Set (Power R 1)) (Power.left z) ∧ T (Power.right z)) :=
    M.product_mem huniv hT
  have hQ : M.S (1 + 1) (setInter (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)
      (fun z : Power R (1 + 1) =>
        setCompl (setEmpty : Set (Power R 1)) (Power.left z) ∧ T (Power.right z))) :=
    M.inter_mem f.graph_mem hP
  have hproj := M.project_mem (1 : Fin (1 + 1)) hQ
  have hEq : (fun y : Power R 1 => ∃ x : Power R (1 + 1),
      setInter (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)
        (fun z : Power R (1 + 1) =>
          setCompl (setEmpty : Set (Power R 1)) (Power.left z) ∧ T (Power.right z)) x ∧
      Power.deleteCoord (1 : Fin (1 + 1)) x = y)
      = (fun y : Power R 1 => ∃ hy : I y, T (f.toFun (Subtype.mk y hy)).1) := by
    funext y
    apply propext
    constructor
    · rintro ⟨z, ⟨⟨hx, hgr⟩, -, hTz⟩, hdel⟩
      have hleft : Power.left z = y := by
        apply power1_ext
        have : (Power.deleteCoord (1 : Fin (1 + 1)) z) 0 = y 0 := by rw [hdel]
        exact this
      have hy : I y := hleft ▸ hx
      refine ⟨hy, ?_⟩
      have hsub : (Subtype.mk y hy : {x : Power R 1 // I x}) = Subtype.mk (Power.left z) hx :=
        Subtype.ext hleft.symm
      have hval : (f.toFun (Subtype.mk y hy)).1 = Power.right z := by
        rw [hgr, hsub]
      rw [hval]
      exact hTz
    · rintro ⟨hy, hTy⟩
      refine ?_
      let z : Power R (1 + 1) :=
        fun i => if i.val = 0 then y 0 else (f.toFun (Subtype.mk y hy)).1 0
      have hleft : Power.left z = y := power1_ext rfl
      have hright : Power.right z = (f.toFun (Subtype.mk y hy)).1 := power1_ext rfl
      have hIz : I (Power.left z) := by rw [hleft]; exact hy
      refine ⟨z, ⟨⟨hIz, ?_⟩, ⟨fun h => False.elim h, ?_⟩⟩, power1_ext rfl⟩
      · have hsub : (Subtype.mk y hy : {x : Power R 1 // I x}) = Subtype.mk (Power.left z) hIz :=
          Subtype.ext hleft.symm
        rw [hright, hsub]
      · rw [hright]
        exact hTy
  rw [hEq] at hproj
  exact hproj

end Monotonicity_Theorem


/-! ### Dichotomy -/


namespace Monotonicity_Theorem

private def endpointList {R : Type} : Endpoint R → List R
  | .negInf => []
  | .finite a => [a]
  | .posInf => []

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

/-- Child A3: a definable subset of the line has finitely many boundary points: outside a finite
set, every open interval is either contained in it or disjoint from it. -/
theorem definable_interval_dichotomy {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {S : Set (Power R 1)} (hS : FiniteUnionOfPointsAndIntervals D S) :
    ∃ F : Set (Power R 1), IsFinite1 F ∧
      ∀ u v : R, D.lt u v →
        (∀ x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x → ¬ F x) →
        ((openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset S ∨
          ∀ x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x → ¬ S x) := by
  induction hS with
  | empty =>
      refine ⟨fun _ => False, ⟨[], fun x => ⟨False.elim, fun h => absurd h (by simp)⟩⟩, ?_⟩
      intro u v _ _
      exact Or.inr fun x _ h => h
  | point a =>
      refine ⟨pointSet a, ⟨[a], fun x => by simp [pointSet, Power.coord1]⟩, ?_⟩
      intro u v _ havoid
      exact Or.inr fun x hx => havoid x hx
  | interval p q =>
      refine ⟨fun x => Power.coord1 x ∈ endpointList p ++ endpointList q,
        ⟨endpointList p ++ endpointList q, fun x => Iff.rfl⟩, ?_⟩
      intro u v huv havoid
      by_cases hmeet : ∃ x : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) x ∧ openInterval D p q x
      · obtain ⟨x, hxJ, hxS⟩ := hmeet
        refine Or.inl ?_
        intro y hyJ
        refine ⟨?_, ?_⟩
        · -- left endpoint
          cases p with
          | negInf => trivial
          | posInf => exact absurd hxS.1 (by simp [Endpoint.lt])
          | finite a =>
              have hax : D.lt a (x 0) := hxS.1
              have hmem : a ∈ endpointList (Endpoint.finite a) ++ endpointList q :=
                List.mem_append_left _ (by simp [endpointList])
              rcases D.trichotomy a (y 0) with h | h | h
              · exact h.1
              · exact absurd (havoid y hyJ) (by
                  simp only [not_not]
                  have : y 0 = a := h.1.symm
                  rw [Power.coord1, this]; exact hmem)
              · exact absurd (havoid (fun _ => a) ⟨D.trans hyJ.1 h.1, D.trans hax hxJ.2⟩)
                  (not_not_intro hmem)
        · -- right endpoint
          cases q with
          | posInf => trivial
          | negInf => exact absurd hxS.2 (by simp [Endpoint.lt])
          | finite c =>
              have hxc : D.lt (x 0) c := hxS.2
              have hmem : c ∈ endpointList p ++ endpointList (Endpoint.finite c) :=
                List.mem_append_right _ (by simp [endpointList])
              rcases D.trichotomy (y 0) c with h | h | h
              · exact h.1
              · exact absurd (havoid y hyJ) (by
                  simp only [not_not]
                  rw [Power.coord1, h.1]; exact hmem)
              · exact absurd (havoid (fun _ => c) ⟨D.trans hxJ.1 hxc, D.trans h.1 hyJ.2⟩)
                  (not_not_intro hmem)
      · refine Or.inr ?_
        intro x hxJ hxS
        exact hmeet ⟨x, hxJ, hxS⟩
  | union hA hB ihA ihB =>
      obtain ⟨FA, hFAfin, hFA⟩ := ihA
      obtain ⟨FB, hFBfin, hFB⟩ := ihB
      refine ⟨fun x => FA x ∨ FB x, isFinite1_or hFAfin hFBfin, ?_⟩
      intro u v huv havoid
      rcases hFA u v huv (fun x hx h => havoid x hx (Or.inl h)) with hA' | hA'
      · exact Or.inl fun x hx => Or.inl (hA' hx)
      · rcases hFB u v huv (fun x hx h => havoid x hx (Or.inr h)) with hB' | hB'
        · exact Or.inl fun x hx => Or.inr (hB' hx)
        · exact Or.inr fun x hx h => h.elim (hA' x hx) (hB' x hx)


end Monotonicity_Theorem


/-! ### IntervalTools -/


namespace Monotonicity_Theorem

variable {R : Type}

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

/-- Inside any nonempty open interval one can find a subinterval avoiding a given finite set. -/
lemma exists_subinterval_avoiding_finite (D : DenseLinearOrderNoEndpoints R)
    {F : Set (Power R 1)} (hF : IsFinite1 F) (u v : R) (huv : D.lt u v) :
    ∃ u₁ v₁ : R, D.lt u₁ v₁ ∧
      (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x →
        openInterval D (Endpoint.finite u) (Endpoint.finite v) x) ∧
      (∀ x : Power R 1, openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x → ¬ F x) := by
  obtain ⟨L, hL⟩ := hF
  obtain ⟨u₁, v₁, huv₁, hsub, havoid⟩ := exists_subinterval_avoiding_list D L u v huv
  exact ⟨u₁, v₁, huv₁, hsub, fun x hx hFx => havoid x hx ((hL x).1 hFx)⟩

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

/-- A nonempty subset of the line contained in a finite list has a least element. -/
lemma exists_least_of_list (D : DenseLinearOrderNoEndpoints R) :
    ∀ (L : List R) (S : R → Prop) (y₀ : R), S y₀ → (∀ a, S a → a ∈ L) →
      ∃ m : R, S m ∧ ∀ z : R, S z → ¬ D.lt z m := by
  intro L
  induction L with
  | nil =>
      intro S y₀ hy₀ hsub
      exact absurd (hsub y₀ hy₀) (by simp)
  | cons a L ih =>
      intro S y₀ hy₀ hsub
      by_cases htail : ∃ y, S y ∧ y ∈ L
      · obtain ⟨y₁, hy₁S, hy₁L⟩ := htail
        obtain ⟨m, hmS, hmin⟩ :=
          ih (fun t => S t ∧ t ∈ L) y₁ ⟨hy₁S, hy₁L⟩ (fun t ht => ht.2)
        by_cases hSa : S a
        · rcases D.trichotomy a m with h | h | h
          · refine ⟨a, hSa, ?_⟩
            intro z hz hza
            rcases List.mem_cons.1 (hsub z hz) with rfl | hzL
            · exact D.irrefl _ hza
            · exact hmin z ⟨hz, hzL⟩ (D.trans hza h.1)
          · refine ⟨m, hmS.1, ?_⟩
            intro z hz hzm
            rcases List.mem_cons.1 (hsub z hz) with rfl | hzL
            · exact D.irrefl _ (h.1 ▸ hzm)
            · exact hmin z ⟨hz, hzL⟩ hzm
          · refine ⟨m, hmS.1, ?_⟩
            intro z hz hzm
            rcases List.mem_cons.1 (hsub z hz) with rfl | hzL
            · exact h.2.1 hzm
            · exact hmin z ⟨hz, hzL⟩ hzm
        · refine ⟨m, hmS.1, ?_⟩
          intro z hz hzm
          rcases List.mem_cons.1 (hsub z hz) with rfl | hzL
          · exact hSa hz
          · exact hmin z ⟨hz, hzL⟩ hzm
      · have hall : ∀ z, S z → z = a := by
          intro z hz
          rcases List.mem_cons.1 (hsub z hz) with h | h
          · exact h
          · exact absurd ⟨z, hz, h⟩ htail
        refine ⟨y₀, hy₀, ?_⟩
        intro z hz hlt
        rw [hall z hz, hall y₀ hy₀] at hlt
        exact D.irrefl _ hlt

end Monotonicity_Theorem


/-! ### OrderTools -/


namespace Monotonicity_Theorem

section OrderTools

variable {R : Type}

/-- The order reversed. -/
def revOrder (D : DenseLinearOrderNoEndpoints R) : DenseLinearOrderNoEndpoints R where
  lt a b := D.lt b a
  irrefl a := D.irrefl a
  trans h1 h2 := D.trans h2 h1
  trichotomy a b := by
    rcases D.trichotomy a b with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ⟨h.1, h.2.2, h.2.1⟩)
    · exact Or.inl h
  dense h := by
    obtain ⟨z, h1, h2⟩ := D.dense h
    exact ⟨z, h2, h1⟩
  no_left_endpoint x := D.no_right_endpoint x
  no_right_endpoint x := D.no_left_endpoint x

/-- Transitivity across a possibly infinite right endpoint. -/
lemma endpoint_lt_trans (D : DenseLinearOrderNoEndpoints R) {t a : R} {q : Endpoint R}
    (h1 : D.lt t a) (h2 : Endpoint.lt D (Endpoint.finite a) q) :
    Endpoint.lt D (Endpoint.finite t) q := by
  cases q with
  | negInf => exact absurd h2 (by simp [Endpoint.lt])
  | posInf => trivial
  | finite b => exact D.trans h1 h2

/-- A nonempty subset of the line contained in a finite list has a greatest element. -/
lemma exists_greatest_of_list (D : DenseLinearOrderNoEndpoints R)
    (L : List R) (S : R → Prop) (y₀ : R) (hy₀ : S y₀) (hsub : ∀ a, S a → a ∈ L) :
    ∃ m : R, S m ∧ ∀ z : R, S z → ¬ D.lt m z :=
  exists_least_of_list (revOrder D) L S y₀ hy₀ hsub

/-- A nonempty finite subset of the line has a greatest element. -/
lemma exists_greatest_of_finite (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (hA : IsFinite1 A) {y₀ : R} (hy₀ : A (pt y₀)) :
    ∃ m : R, A (pt m) ∧ ∀ z : R, A (pt z) → ¬ D.lt m z := by
  obtain ⟨L, hL⟩ := hA
  exact exists_greatest_of_list D L (fun a => A (pt a)) y₀ hy₀ (fun a ha => (hL (pt a)).1 ha)

/-- A nonempty finite subset of the line has a least element. -/
lemma exists_least_of_finite (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (hA : IsFinite1 A) {y₀ : R} (hy₀ : A (pt y₀)) :
    ∃ m : R, A (pt m) ∧ ∀ z : R, A (pt z) → ¬ D.lt z m := by
  obtain ⟨L, hL⟩ := hA
  exact exists_least_of_list D L (fun a => A (pt a)) y₀ hy₀ (fun a ha => (hL (pt a)).1 ha)

/-- A definable subset of the line containing no nonempty open interval is finite. -/
lemma isFinite1_of_no_interval (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (hA : FiniteUnionOfPointsAndIntervals D A)
    (hno : ∀ p q : R, D.lt p q →
      ¬ (openInterval D (Endpoint.finite p) (Endpoint.finite q)).Subset A) :
    IsFinite1 A := by
  by_contra hinf
  obtain ⟨p, q, hpq, hsub⟩ := infinite_contains_interval D hA hinf
  exact hno p q hpq hsub

/-- A nonempty definable subset of the line which is bounded below by `x` has a greatest lower
bound `z ≥ x`; moreover either `z` belongs to the set, or the set contains a right neighbourhood
of `z`. -/
lemma exists_inf_of_definable (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (hA : FiniteUnionOfPointsAndIntervals D A) :
    ∀ x : R, (∃ a : R, D.lt x a ∧ A (pt a)) →
      ∃ z : R, ¬ D.lt z x ∧ (∀ a : R, D.lt x a → A (pt a) → ¬ D.lt a z) ∧
        (A (pt z) ∨ ∃ w : R, D.lt z w ∧ ∀ t : R, D.lt z t → D.lt t w → A (pt t)) := by
  induction hA with
  | empty =>
      intro _ hne
      obtain ⟨_, _, ha⟩ := hne
      exact absurd ha (fun h => h)
  | point a =>
      intro x hne
      obtain ⟨b, hxb, hb⟩ := hne
      have hba : b = a := hb
      refine ⟨b, fun h => D.irrefl _ (D.trans hxb h), ?_, Or.inl hb⟩
      intro c _ hc hcb
      have hca : c = a := hc
      rw [hca, ← hba] at hcb
      exact D.irrefl _ hcb
  | interval p q =>
      intro x hne
      obtain ⟨a, hxa, ha⟩ := hne
      have haq : Endpoint.lt D (Endpoint.finite a) q := ha.2
      have hpa : Endpoint.lt D p (Endpoint.finite a) := ha.1
      by_cases hcase : ∃ b : R, p = Endpoint.finite b ∧ ¬ D.lt b x
      · obtain ⟨b, hpb, hbx⟩ := hcase
        refine ⟨b, hbx, ?_, Or.inr ⟨a, ?_, ?_⟩⟩
        · intro c _ hc hcb
          have : D.lt b (c) := by
            have := hc.1
            rw [hpb] at this
            exact this
          exact D.irrefl _ (D.trans this hcb)
        · rw [hpb] at hpa; exact hpa
        · intro t hbt hta
          refine ⟨?_, endpoint_lt_trans D hta haq⟩
          rw [hpb]
          exact hbt
      · refine ⟨x, fun h => D.irrefl _ h, fun c hxc _ hcx => D.irrefl _ (D.trans hxc hcx),
          Or.inr ⟨a, hxa, ?_⟩⟩
        intro t hxt hta
        refine ⟨?_, endpoint_lt_trans D hta haq⟩
        cases p with
        | negInf => trivial
        | posInf => exact absurd hpa (by simp [Endpoint.lt])
        | finite b =>
            have hbx : D.lt b x := by
              by_contra hcon
              exact hcase ⟨b, rfl, hcon⟩
            exact D.trans hbx hxt
  | @union A0 B0 hA' hB' ihA ihB =>
      intro x hne
      by_cases hAne : ∃ a : R, D.lt x a ∧ A0 (pt a)
      · obtain ⟨zA, hzA0, hzA1, hzA2⟩ := ihA x hAne
        by_cases hBne : ∃ a : R, D.lt x a ∧ B0 (pt a)
        · obtain ⟨zB, hzB0, hzB1, hzB2⟩ := ihB x hBne
          rcases D.trichotomy zA zB with h | h | h
          · refine ⟨zA, hzA0, ?_, ?_⟩
            · intro c hxc hc hcz
              rcases hc with hc | hc
              · exact hzA1 c hxc hc hcz
              · exact hzB1 c hxc hc (D.trans hcz h.1)
            · rcases hzA2 with hm | ⟨w, hw1, hw2⟩
              · exact Or.inl (Or.inl hm)
              · exact Or.inr ⟨w, hw1, fun t h1 h2 => Or.inl (hw2 t h1 h2)⟩
          · refine ⟨zA, hzA0, ?_, ?_⟩
            · intro c hxc hc hcz
              rcases hc with hc | hc
              · exact hzA1 c hxc hc hcz
              · exact hzB1 c hxc hc (by rw [← h.1]; exact hcz)
            · rcases hzA2 with hm | ⟨w, hw1, hw2⟩
              · exact Or.inl (Or.inl hm)
              · exact Or.inr ⟨w, hw1, fun t h1 h2 => Or.inl (hw2 t h1 h2)⟩
          · refine ⟨zB, hzB0, ?_, ?_⟩
            · intro c hxc hc hcz
              rcases hc with hc | hc
              · exact hzA1 c hxc hc (D.trans hcz h.1)
              · exact hzB1 c hxc hc hcz
            · rcases hzB2 with hm | ⟨w, hw1, hw2⟩
              · exact Or.inl (Or.inr hm)
              · exact Or.inr ⟨w, hw1, fun t h1 h2 => Or.inr (hw2 t h1 h2)⟩
        · refine ⟨zA, hzA0, ?_, ?_⟩
          · intro c hxc hc hcz
            rcases hc with hc | hc
            · exact hzA1 c hxc hc hcz
            · exact hBne ⟨c, hxc, hc⟩
          · rcases hzA2 with hm | ⟨w, hw1, hw2⟩
            · exact Or.inl (Or.inl hm)
            · exact Or.inr ⟨w, hw1, fun t h1 h2 => Or.inl (hw2 t h1 h2)⟩
      · have hBne : ∃ a : R, D.lt x a ∧ B0 (pt a) := by
          obtain ⟨a, hxa, ha⟩ := hne
          rcases ha with ha | ha
          · exact absurd ⟨a, hxa, ha⟩ hAne
          · exact ⟨a, hxa, ha⟩
        obtain ⟨zB, hzB0, hzB1, hzB2⟩ := ihB x hBne
        refine ⟨zB, hzB0, ?_, ?_⟩
        · intro c hxc hc hcz
          rcases hc with hc | hc
          · exact hAne ⟨c, hxc, hc⟩
          · exact hzB1 c hxc hc hcz
        · rcases hzB2 with hm | ⟨w, hw1, hw2⟩
          · exact Or.inl (Or.inr hm)
          · exact Or.inr ⟨w, hw1, fun t h1 h2 => Or.inr (hw2 t h1 h2)⟩

/-- Reverse an endpoint symbol. -/
def revEnd : Endpoint R → Endpoint R
  | Endpoint.negInf => Endpoint.posInf
  | Endpoint.finite a => Endpoint.finite a
  | Endpoint.posInf => Endpoint.negInf

lemma endpoint_lt_rev1 (D : DenseLinearOrderNoEndpoints R) (e : Endpoint R) (x : R) :
    Endpoint.lt (revOrder D) (revEnd e) (Endpoint.finite x)
      ↔ Endpoint.lt D (Endpoint.finite x) e := by
  cases e <;> exact Iff.rfl

lemma endpoint_lt_rev2 (D : DenseLinearOrderNoEndpoints R) (e : Endpoint R) (x : R) :
    Endpoint.lt (revOrder D) (Endpoint.finite x) (revEnd e)
      ↔ Endpoint.lt D e (Endpoint.finite x) := by
  cases e <;> exact Iff.rfl

/-- Definable subsets of the line are the same for the reversed order. -/
lemma fupi_rev (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (h : FiniteUnionOfPointsAndIntervals D A) :
    FiniteUnionOfPointsAndIntervals (revOrder D) A := by
  induction h with
  | empty => exact FiniteUnionOfPointsAndIntervals.empty
  | point a => exact FiniteUnionOfPointsAndIntervals.point a
  | interval p q =>
      have hset : openInterval D p q = openInterval (revOrder D) (revEnd q) (revEnd p) := by
        funext x
        apply propext
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨(endpoint_lt_rev1 D q (x 0)).2 h2, (endpoint_lt_rev2 D p (x 0)).2 h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(endpoint_lt_rev2 D p (x 0)).1 h2, (endpoint_lt_rev1 D q (x 0)).1 h1⟩
      rw [hset]
      exact FiniteUnionOfPointsAndIntervals.interval _ _
  | union _ _ ih1 ih2 => exact FiniteUnionOfPointsAndIntervals.union ih1 ih2

/-- A nonempty definable subset of the line which is bounded above by `x` has a least upper
bound `z ≤ x`; moreover either `z` belongs to the set, or the set contains a left neighbourhood
of `z`. -/
lemma exists_sup_of_definable (D : DenseLinearOrderNoEndpoints R) {A : Set (Power R 1)}
    (hA : FiniteUnionOfPointsAndIntervals D A) :
    ∀ x : R, (∃ a : R, D.lt a x ∧ A (pt a)) →
      ∃ z : R, ¬ D.lt x z ∧ (∀ a : R, D.lt a x → A (pt a) → ¬ D.lt z a) ∧
        (A (pt z) ∨ ∃ w : R, D.lt w z ∧ ∀ t : R, D.lt t z → D.lt w t → A (pt t)) :=
  exists_inf_of_definable (revOrder D) (fupi_rev D hA)

end OrderTools

end Monotonicity_Theorem


/-! ### Definability -/


namespace Monotonicity_Theorem

section Toolkit

variable {R : Type}

/-- The reindexing map sending `0` to `i` and `1` to `j`. -/
def pair2 {n : Nat} (i j : Fin n) : Fin 2 → Fin n := fun k => if k = 0 then i else j

lemma defin_lt {n : Nat} {D : DenseLinearOrderNoEndpoints R} (M : OMinimalStructure D)
    (i j : Fin n) : M.S n (fun t : Power R n => D.lt (t i) (t j)) :=
  M.reindex_mem (pair2 i j) M.lt_mem

lemma defin_at {n : Nat} {D : DenseLinearOrderNoEndpoints R} (M : OMinimalStructure D)
    (i : Fin n) {A : Set (Power R 1)} (hA : M.S 1 A) :
    M.S n (fun t : Power R n => A (fun _ => t i)) :=
  M.reindex_mem (fun _ : Fin 1 => i) hA

lemma defin_eq {n : Nat} {D : DenseLinearOrderNoEndpoints R} (M : OMinimalStructure D)
    (i j : Fin n) : M.S n (fun t : Power R n => t i = t j) :=
  M.reindex_mem (pair2 i j) (M.diagonal_mem 0 1 (by decide))

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

lemma exists_power2 {P : R → R → Prop} : (∃ y : Power R 2, P (y 0) (y 1)) ↔ ∃ a b : R, P a b := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y 0, y 1, h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨fun k => if k.val = 0 then a else b, h⟩

lemma exists_power4 {P : R → R → R → R → Prop} :
    (∃ y : Power R 4, P (y 0) (y 1) (y 2) (y 3)) ↔ ∃ a b c d : R, P a b c d := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y 0, y 1, y 2, y 3, h⟩
  · rintro ⟨a, b, c, d, h⟩
    exact ⟨fun k => if k.val = 0 then a else if k.val = 1 then b else if k.val = 2 then c else d, h⟩

lemma exists_power1 {P : R → Prop} : (∃ y : Power R 1, P (y 0)) ↔ ∃ a : R, P a := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y 0, h⟩
  · rintro ⟨a, h⟩
    exact ⟨fun _ => a, h⟩

/-- A window locus built from a definable two-variable property is definable. -/
lemma locus_definable {D : DenseLinearOrderNoEndpoints R} (M : OMinimalStructure D)
    (P : R → R → Prop) (hP : M.S 2 (fun p : Power R 2 => P (p 0) (p 1))) :
    M.S 1 (fun x : Power R 1 => ∃ u v : R, D.lt u (x 0) ∧ D.lt (x 0) v ∧ P u v) := by
  have h1 : M.S 3 (fun s : Power R 3 => D.lt (s 1) (s 0)) := defin_lt M 1 0
  have h2 : M.S 3 (fun s : Power R 3 => D.lt (s 0) (s 2)) := defin_lt M 0 2
  have h3 : M.S 3 (fun s : Power R 3 => P (s 1) (s 2)) := M.reindex_mem (pair2 1 2) hP
  have h4 : M.S 3 (fun s : Power R 3 => D.lt (s 1) (s 0) ∧ D.lt (s 0) (s 2) ∧ P (s 1) (s 2)) :=
    M.inter_mem h1 (M.inter_mem h2 h3)
  have h5 := M.existsLast_mem (n := 1) (m := 2) h4
  have hset : (fun x : Power R 1 => ∃ y : Power R 2,
      (fun s : Power R 3 => D.lt (s 1) (s 0) ∧ D.lt (s 0) (s 2) ∧ P (s 1) (s 2))
        (Power.append x y))
      = (fun x : Power R 1 => ∃ u v : R, D.lt u (x 0) ∧ D.lt (x 0) v ∧ P u v) := by
    funext x
    exact propext (exists_power2 (P := fun a b => D.lt a (x 0) ∧ D.lt (x 0) b ∧ P a b))
  rw [hset] at h5
  exact h5

end Toolkit

section Properties

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

private lemma pt_eq (x : Power R 1) : (fun _ : Fin 1 => x 0) = x := power1_ext rfl

/-- Constancy on an interval is a definable condition on the endpoints. -/
lemma const_prop_definable (f : DefinableFunction M I B) :
    M.S 2 (fun p : Power R 2 => ConstOnInterval f (p 0) (p 1)) := by
  have hbad : M.S 6 (fun t : Power R 6 =>
      (∃ h : I (fun _ => t 2),
        (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
      (∃ h : I (fun _ => t 3),
        (fun _ => t 5 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 3) h)).1) ∧
      D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ D.lt (t 0) (t 3) ∧ D.lt (t 3) (t 1) ∧
      ¬ (t 4 = t 5)) :=
    M.inter_mem (defin_graph f 2 4) (M.inter_mem (defin_graph f 3 5)
      (M.inter_mem (defin_lt M 0 2) (M.inter_mem (defin_lt M 2 1)
        (M.inter_mem (defin_lt M 0 3) (M.inter_mem (defin_lt M 3 1)
          (M.compl_mem (defin_eq M 4 5)))))))
  have hex := M.existsLast_mem (n := 2) (m := 4) hbad
  have hcompl := M.compl_mem hex
  have hset : (setCompl (fun p : Power R 2 => ∃ y : Power R 4,
      (fun t : Power R 6 =>
        (∃ h : I (fun _ => t 2),
          (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
        (∃ h : I (fun _ => t 3),
          (fun _ => t 5 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 3) h)).1) ∧
        D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ D.lt (t 0) (t 3) ∧ D.lt (t 3) (t 1) ∧
        ¬ (t 4 = t 5)) (Power.append p y)))
      = (fun p : Power R 2 => ConstOnInterval f (p 0) (p 1)) := by
    funext p
    apply propext
    constructor
    · intro hno x hx hxJ z hz hzJ
      by_contra hne
      refine hno ?_
      refine (exists_power4 (P := fun a b c d =>
        (∃ h : I (fun _ => a), (fun _ => c : Power R 1) = (f.toFun (Subtype.mk (fun _ => a) h)).1) ∧
        (∃ h : I (fun _ => b), (fun _ => d : Power R 1) = (f.toFun (Subtype.mk (fun _ => b) h)).1) ∧
        D.lt (p 0) a ∧ D.lt a (p 1) ∧ D.lt (p 0) b ∧ D.lt b (p 1) ∧ ¬ (c = d))).2 ?_
      refine ⟨x 0, z 0, (f.toFun (Subtype.mk x hx)).1 0, (f.toFun (Subtype.mk z hz)).1 0, ?_, ?_,
        hxJ.1, hxJ.2, hzJ.1, hzJ.2, ?_⟩
      · refine ⟨(pt_eq x).symm ▸ hx, ?_⟩
        have : (Subtype.mk (fun _ : Fin 1 => x 0) ((pt_eq x).symm ▸ hx) : {w : Power R 1 // I w})
            = Subtype.mk x hx := Subtype.ext (pt_eq x)
        rw [this]
        exact pt_eq _
      · refine ⟨(pt_eq z).symm ▸ hz, ?_⟩
        have : (Subtype.mk (fun _ : Fin 1 => z 0) ((pt_eq z).symm ▸ hz) : {w : Power R 1 // I w})
            = Subtype.mk z hz := Subtype.ext (pt_eq z)
        rw [this]
        exact pt_eq _
      · intro hcd
        exact hne (Subtype.ext (power1_ext hcd))
    · intro hconst hbad'
      obtain ⟨a, b, c, d, ⟨h1, e1⟩, ⟨h2, e2⟩, l1, l2, l3, l4, hne⟩ :=
        (exists_power4 (P := fun a b c d =>
          (∃ h : I (fun _ => a),
            (fun _ => c : Power R 1) = (f.toFun (Subtype.mk (fun _ => a) h)).1) ∧
          (∃ h : I (fun _ => b),
            (fun _ => d : Power R 1) = (f.toFun (Subtype.mk (fun _ => b) h)).1) ∧
          D.lt (p 0) a ∧ D.lt a (p 1) ∧ D.lt (p 0) b ∧ D.lt b (p 1) ∧ ¬ (c = d))).1 hbad'
      have heq := hconst (fun _ => a) h1 ⟨l1, l2⟩ (fun _ => b) h2 ⟨l3, l4⟩
      apply hne
      have : (fun _ : Fin 1 => c) = (fun _ : Fin 1 => d) := by
        rw [e1, e2, heq]
      exact congrFun this 0
  rw [hset] at hcompl
  exact hcompl

/-- Strict increase on an interval is a definable condition on the endpoints. -/
lemma inc_prop_definable (f : DefinableFunction M I B) :
    M.S 2 (fun p : Power R 2 => IncOnInterval f (p 0) (p 1)) := by
  have hbad : M.S 6 (fun t : Power R 6 =>
      (∃ h : I (fun _ => t 2),
        (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
      (∃ h : I (fun _ => t 3),
        (fun _ => t 5 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 3) h)).1) ∧
      D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ D.lt (t 0) (t 3) ∧ D.lt (t 3) (t 1) ∧
      D.lt (t 2) (t 3) ∧ ¬ (D.lt (t 4) (t 5))) :=
    M.inter_mem (defin_graph f 2 4) (M.inter_mem (defin_graph f 3 5)
      (M.inter_mem (defin_lt M 0 2) (M.inter_mem (defin_lt M 2 1)
        (M.inter_mem (defin_lt M 0 3) (M.inter_mem (defin_lt M 3 1)
          (M.inter_mem (defin_lt M 2 3) (M.compl_mem (defin_lt M 4 5))))))))
  have hex := M.existsLast_mem (n := 2) (m := 4) hbad
  have hcompl := M.compl_mem hex
  have hset : (setCompl (fun p : Power R 2 => ∃ y : Power R 4,
      (fun t : Power R 6 =>
        (∃ h : I (fun _ => t 2),
          (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
        (∃ h : I (fun _ => t 3),
          (fun _ => t 5 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 3) h)).1) ∧
        D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ D.lt (t 0) (t 3) ∧ D.lt (t 3) (t 1) ∧
        D.lt (t 2) (t 3) ∧ ¬ (D.lt (t 4) (t 5))) (Power.append p y)))
      = (fun p : Power R 2 => IncOnInterval f (p 0) (p 1)) := by
    funext p
    apply propext
    constructor
    · intro hno x hx hxJ z hz hzJ hxz
      by_contra hne
      refine hno ?_
      refine (exists_power4 (P := fun a b c d =>
        (∃ h : I (fun _ => a), (fun _ => c : Power R 1) = (f.toFun (Subtype.mk (fun _ => a) h)).1) ∧
        (∃ h : I (fun _ => b), (fun _ => d : Power R 1) = (f.toFun (Subtype.mk (fun _ => b) h)).1) ∧
        D.lt (p 0) a ∧ D.lt a (p 1) ∧ D.lt (p 0) b ∧ D.lt b (p 1) ∧
        D.lt a b ∧ ¬ (D.lt c d))).2 ?_
      refine ⟨x 0, z 0, (f.toFun (Subtype.mk x hx)).1 0, (f.toFun (Subtype.mk z hz)).1 0, ?_, ?_,
        hxJ.1, hxJ.2, hzJ.1, hzJ.2, hxz, hne⟩
      · refine ⟨(pt_eq x).symm ▸ hx, ?_⟩
        have hs : (Subtype.mk (fun _ : Fin 1 => x 0) ((pt_eq x).symm ▸ hx) : {w : Power R 1 // I w})
            = Subtype.mk x hx := Subtype.ext (pt_eq x)
        rw [hs]
        exact pt_eq _
      · refine ⟨(pt_eq z).symm ▸ hz, ?_⟩
        have hs : (Subtype.mk (fun _ : Fin 1 => z 0) ((pt_eq z).symm ▸ hz) : {w : Power R 1 // I w})
            = Subtype.mk z hz := Subtype.ext (pt_eq z)
        rw [hs]
        exact pt_eq _
    · intro hinc hbad'
      obtain ⟨a, b, c, d, ⟨h1, e1⟩, ⟨h2, e2⟩, l1, l2, l3, l4, lab, hne⟩ :=
        (exists_power4 (P := fun a b c d =>
          (∃ h : I (fun _ => a),
            (fun _ => c : Power R 1) = (f.toFun (Subtype.mk (fun _ => a) h)).1) ∧
          (∃ h : I (fun _ => b),
            (fun _ => d : Power R 1) = (f.toFun (Subtype.mk (fun _ => b) h)).1) ∧
          D.lt (p 0) a ∧ D.lt a (p 1) ∧ D.lt (p 0) b ∧ D.lt b (p 1) ∧
          D.lt a b ∧ ¬ (D.lt c d))).1 hbad'
      refine hne ?_
      have hstep := hinc (fun _ => a) h1 ⟨l1, l2⟩ (fun _ => b) h2 ⟨l3, l4⟩ lab
      have hc : c = (f.toFun (Subtype.mk (fun _ => a) h1)).1 0 := congrFun e1 0
      have hd : d = (f.toFun (Subtype.mk (fun _ => b) h2)).1 0 := congrFun e2 0
      rw [hc, hd]
      exact hstep
  rw [hset] at hcompl
  exact hcompl

/-- Strict decrease on an interval is a definable condition on the endpoints. -/
lemma dec_prop_definable (f : DefinableFunction M I B) :
    M.S 2 (fun p : Power R 2 => DecOnInterval f (p 0) (p 1)) := by
  have hbad : M.S 6 (fun t : Power R 6 =>
      (∃ h : I (fun _ => t 2),
        (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
      (∃ h : I (fun _ => t 3),
        (fun _ => t 5 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 3) h)).1) ∧
      D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ D.lt (t 0) (t 3) ∧ D.lt (t 3) (t 1) ∧
      D.lt (t 2) (t 3) ∧ ¬ (D.lt (t 5) (t 4))) :=
    M.inter_mem (defin_graph f 2 4) (M.inter_mem (defin_graph f 3 5)
      (M.inter_mem (defin_lt M 0 2) (M.inter_mem (defin_lt M 2 1)
        (M.inter_mem (defin_lt M 0 3) (M.inter_mem (defin_lt M 3 1)
          (M.inter_mem (defin_lt M 2 3) (M.compl_mem (defin_lt M 5 4))))))))
  have hex := M.existsLast_mem (n := 2) (m := 4) hbad
  have hcompl := M.compl_mem hex
  have hset : (setCompl (fun p : Power R 2 => ∃ y : Power R 4,
      (fun t : Power R 6 =>
        (∃ h : I (fun _ => t 2),
          (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
        (∃ h : I (fun _ => t 3),
          (fun _ => t 5 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 3) h)).1) ∧
        D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ D.lt (t 0) (t 3) ∧ D.lt (t 3) (t 1) ∧
        D.lt (t 2) (t 3) ∧ ¬ (D.lt (t 5) (t 4))) (Power.append p y)))
      = (fun p : Power R 2 => DecOnInterval f (p 0) (p 1)) := by
    funext p
    apply propext
    constructor
    · intro hno x hx hxJ z hz hzJ hxz
      by_contra hne
      refine hno ?_
      refine (exists_power4 (P := fun a b c d =>
        (∃ h : I (fun _ => a), (fun _ => c : Power R 1) = (f.toFun (Subtype.mk (fun _ => a) h)).1) ∧
        (∃ h : I (fun _ => b), (fun _ => d : Power R 1) = (f.toFun (Subtype.mk (fun _ => b) h)).1) ∧
        D.lt (p 0) a ∧ D.lt a (p 1) ∧ D.lt (p 0) b ∧ D.lt b (p 1) ∧
        D.lt a b ∧ ¬ (D.lt d c))).2 ?_
      refine ⟨x 0, z 0, (f.toFun (Subtype.mk x hx)).1 0, (f.toFun (Subtype.mk z hz)).1 0, ?_, ?_,
        hxJ.1, hxJ.2, hzJ.1, hzJ.2, hxz, hne⟩
      · refine ⟨(pt_eq x).symm ▸ hx, ?_⟩
        have hs : (Subtype.mk (fun _ : Fin 1 => x 0) ((pt_eq x).symm ▸ hx) : {w : Power R 1 // I w})
            = Subtype.mk x hx := Subtype.ext (pt_eq x)
        rw [hs]
        exact pt_eq _
      · refine ⟨(pt_eq z).symm ▸ hz, ?_⟩
        have hs : (Subtype.mk (fun _ : Fin 1 => z 0) ((pt_eq z).symm ▸ hz) : {w : Power R 1 // I w})
            = Subtype.mk z hz := Subtype.ext (pt_eq z)
        rw [hs]
        exact pt_eq _
    · intro hdec hbad'
      obtain ⟨a, b, c, d, ⟨h1, e1⟩, ⟨h2, e2⟩, l1, l2, l3, l4, lab, hne⟩ :=
        (exists_power4 (P := fun a b c d =>
          (∃ h : I (fun _ => a),
            (fun _ => c : Power R 1) = (f.toFun (Subtype.mk (fun _ => a) h)).1) ∧
          (∃ h : I (fun _ => b),
            (fun _ => d : Power R 1) = (f.toFun (Subtype.mk (fun _ => b) h)).1) ∧
          D.lt (p 0) a ∧ D.lt a (p 1) ∧ D.lt (p 0) b ∧ D.lt b (p 1) ∧
          D.lt a b ∧ ¬ (D.lt d c))).1 hbad'
      refine hne ?_
      have hstep := hdec (fun _ => a) h1 ⟨l1, l2⟩ (fun _ => b) h2 ⟨l3, l4⟩ lab
      have hc : c = (f.toFun (Subtype.mk (fun _ => a) h1)).1 0 := congrFun e1 0
      have hd : d = (f.toFun (Subtype.mk (fun _ => b) h2)).1 0 := congrFun e2 0
      rw [hc, hd]
      exact hstep
  rw [hset] at hcompl
  exact hcompl

/-- Containment of an interval in a definable set is a definable condition on the endpoints. -/
lemma subset_prop_definable (hI : M.S 1 I) :
    M.S 2 (fun p : Power R 2 =>
      (openInterval D (Endpoint.finite (p 0)) (Endpoint.finite (p 1))).Subset I) := by
  have hbad : M.S 3 (fun t : Power R 3 =>
      D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ ¬ (I (fun _ => t 2))) :=
    M.inter_mem (defin_lt M 0 2) (M.inter_mem (defin_lt M 2 1)
      (M.compl_mem (defin_at M 2 hI)))
  have hex := M.existsLast_mem (n := 2) (m := 1) hbad
  have hcompl := M.compl_mem hex
  have hset : (setCompl (fun p : Power R 2 => ∃ y : Power R 1,
      (fun t : Power R 3 => D.lt (t 0) (t 2) ∧ D.lt (t 2) (t 1) ∧ ¬ (I (fun _ => t 2)))
        (Power.append p y)))
      = (fun p : Power R 2 =>
          (openInterval D (Endpoint.finite (p 0)) (Endpoint.finite (p 1))).Subset I) := by
    funext p
    apply propext
    constructor
    · intro hno x hxJ
      by_contra hxI
      refine hno ?_
      refine (exists_power1 (P := fun a =>
        D.lt (p 0) a ∧ D.lt a (p 1) ∧ ¬ (I (fun _ => a)))).2 ⟨x 0, hxJ.1, hxJ.2, ?_⟩
      rw [pt_eq x]
      exact hxI
    · intro hsub hbad'
      obtain ⟨a, l1, l2, hna⟩ :=
        (exists_power1 (P := fun a => D.lt (p 0) a ∧ D.lt a (p 1) ∧ ¬ (I (fun _ => a)))).1 hbad'
      exact hna (hsub ⟨l1, l2⟩)
  rw [hset] at hcompl
  exact hcompl

/-- Child A1: the three window loci of a definable function are definable. -/
theorem window_loci_definable_proof (f : DefinableFunction M I B) :
    M.S 1 (ConstWindowLocus f) ∧ M.S 1 (IncWindowLocus f) ∧ M.S 1 (DecWindowLocus f) := by
  refine ⟨locus_definable M _ (const_prop_definable f), ?_, ?_⟩
  · exact locus_definable M _
      (M.inter_mem (subset_prop_definable f.domain_mem) (inc_prop_definable f))
  · exact locus_definable M _
      (M.inter_mem (subset_prop_definable f.domain_mem) (dec_prop_definable f))

end Properties

end Monotonicity_Theorem


/-! ### LocalGlobal -/


namespace Monotonicity_Theorem

section Chain

variable {R : Type}

/-- The point of the line with coordinate `t`. -/
def ptOf (t : R) : Power R 1 := fun _ => t

/-- Propagation of a definable property along an interval.

`A` is a definable set, `F` its finite exceptional set given by the interval dichotomy, and `L`
a list of the coordinates of `F`.  Assuming that from any starting point one can find a point of
`A` immediately to the right (`hW`) and that a point of `A` immediately to the left of `y`
forces `y ∈ A` (`hE`), every point of the interval to the right of a starting point is in `A`. -/
lemma chain_propagation (D : DenseLinearOrderNoEndpoints R) (u v : R)
    (A : Set (Power R 1)) (Start : Power R 1 → Prop)
    (F : Set (Power R 1)) (L : List R) (hL : ∀ z : Power R 1, F z ↔ z 0 ∈ L)
    (hdich : ∀ a b : R, D.lt a b →
      (∀ z : Power R 1, openInterval D (Endpoint.finite a) (Endpoint.finite b) z → ¬ F z) →
      ((openInterval D (Endpoint.finite a) (Endpoint.finite b)).Subset A ∨
        ∀ z : Power R 1, openInterval D (Endpoint.finite a) (Endpoint.finite b) z → ¬ A z))
    (hAstart : ∀ z, A z → Start z)
    (hW : ∀ x' y' : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → Start x' → ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t))
    (hE : ∀ y' : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
        D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y') :
    ∀ (l : List R) (x' y' : Power R 1),
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → Start x' →
      (∀ w ∈ L, D.lt (x' 0) w → D.lt w (y' 0) → w ∈ l) → A y' := by
  intro l
  induction l with
  | nil =>
      intro x' y' hx' hy' hlt hstart hcov
      -- no exceptional point lies strictly between `x'` and `y'`
      have havoid : ∀ z : Power R 1,
          openInterval D (Endpoint.finite (x' 0)) (Endpoint.finite (y' 0)) z → ¬ F z := by
        intro z hz hFz
        have := hcov (z 0) ((hL z).1 hFz) hz.1 hz.2
        simp at this
      have hsubA : (openInterval D (Endpoint.finite (x' 0)) (Endpoint.finite (y' 0))).Subset A := by
        rcases hdich (x' 0) (y' 0) hlt havoid with h | h
        · exact h
        · obtain ⟨t, ht₁, ht₂, hAt⟩ := hW x' y' hx' hy' hlt hstart
          exact absurd hAt (h (ptOf t) ⟨ht₁, ht₂⟩)
      -- every point strictly between lies in the ambient interval
      have hbetween : ∀ z : Power R 1,
          openInterval D (Endpoint.finite (x' 0)) (Endpoint.finite (y' 0)) z →
          openInterval D (Endpoint.finite u) (Endpoint.finite v) z :=
        fun z hz => ⟨D.trans hx'.1 hz.1, D.trans hz.2 hy'.2⟩
      obtain ⟨a, ha, hEa⟩ := hE y' hy'
      -- choose a point of `A` between `max a (x' 0)` and `y' 0`
      obtain ⟨s, hs₁, hs₂, hs₃⟩ :
          ∃ s : R, D.lt (x' 0) s ∧ D.lt s (y' 0) ∧ D.lt a s := by
        rcases D.trichotomy a (x' 0) with h | h | h
        · obtain ⟨s, hs₁, hs₂⟩ := D.dense hlt
          exact ⟨s, hs₁, hs₂, D.trans h.1 hs₁⟩
        · obtain ⟨s, hs₁, hs₂⟩ := D.dense hlt
          exact ⟨s, hs₁, hs₂, h.1 ▸ hs₁⟩
        · obtain ⟨s, hs₁, hs₂⟩ := D.dense ha
          exact ⟨s, D.trans h.1 hs₁, hs₂, hs₁⟩
      have hsJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf s) :=
        hbetween (ptOf s) ⟨hs₁, hs₂⟩
      exact hEa (ptOf s) hsJ hs₃ hs₂ (hsubA ⟨hs₁, hs₂⟩)
  | cons c l ih =>
      intro x' y' hx' hy' hlt hstart hcov
      by_cases hc : c ∈ L ∧ D.lt (x' 0) c ∧ D.lt c (y' 0)
      · obtain ⟨hcL, hcx, hcy⟩ := hc
        have hcJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf c) :=
          ⟨D.trans hx'.1 hcx, D.trans hcy hy'.2⟩
        by_cases hAc : A (ptOf c)
        · refine ih (ptOf c) y' hcJ hy' hcy (hAstart _ hAc) ?_
          intro w hw hw₁ hw₂
          have hmem := hcov w hw (D.trans hcx hw₁) hw₂
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact absurd hw₁ (D.irrefl w)
          · exact hmem
        · exfalso
          refine hAc (ih x' (ptOf c) hx' hcJ hcx hstart ?_)
          intro w hw hw₁ hw₂
          have hmem := hcov w hw hw₁ (D.trans hw₂ hcy)
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact absurd hw₂ (D.irrefl w)
          · exact hmem
      · refine ih x' y' hx' hy' hlt hstart ?_
        intro w hw hw₁ hw₂
        have hmem := hcov w hw hw₁ hw₂
        rcases List.mem_cons.1 hmem with rfl | hmem
        · exact absurd ⟨hw, hw₁, hw₂⟩ hc
        · exact hmem

end Chain

section Instances

variable {R : Type}

/-- Choose a point strictly between `x` and `min b y`. -/
private lemma exists_between_of_lt (D : DenseLinearOrderNoEndpoints R) {x y b : R}
    (hxy : D.lt x y) (hxb : D.lt x b) :
    ∃ t : R, D.lt x t ∧ D.lt t y ∧ D.lt t b := by
  rcases D.trichotomy b y with h | h | h
  · obtain ⟨t, h1, h2⟩ := D.dense hxb
    exact ⟨t, h1, D.trans h2 h.1, h2⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hxb
    exact ⟨t, h1, h.1 ▸ h2, h2⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hxy
    exact ⟨t, h1, h2, D.trans h2 h.1⟩

theorem locally_constant_implies_constant (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hloc : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset
      (ConstWindowLocus f)) :
    ConstOnInterval f u v := by
  have key : ∀ x y : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
      D.lt (x 0) (y 0) → ∀ (hxI : I x) (hyI : I y),
        (f.toFun (Subtype.mk x hxI)).1 0 = (f.toFun (Subtype.mk y hyI)).1 0 := by
    intro x y hxJ hyJ hlt hxI hyI
    set c : R := (f.toFun (Subtype.mk x hxI)).1 0 with hc
    set A : Set (Power R 1) :=
      fun z => ∃ hz : I z, pointSet c ((f.toFun (Subtype.mk z hz)).1) with hAdef
    have hA : M.S 1 A :=
      definable_preimage D M f ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.point c))
    obtain ⟨F, hFfin, hdich⟩ := definable_interval_dichotomy D ((M.ominimal A).1 hA)
    obtain ⟨L, hL⟩ := hFfin
    have hW : ∀ x' y' : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
        openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
        D.lt (x' 0) (y' 0) → (x' = x ∨ A x') →
        ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t) := by
      intro x' y' hx'J hy'J hlt' hstart
      obtain ⟨a, b, ha, hb, hconst⟩ := hloc hx'J
      obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_between_of_lt D hlt' hb
      have htJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf t) :=
        ⟨D.trans hx'J.1 ht₁, D.trans ht₂ hy'J.2⟩
      have htI : I (ptOf t) := hsub htJ
      have hx'I : I x' := hsub hx'J
      have hval : f.toFun (Subtype.mk (ptOf t) htI) = f.toFun (Subtype.mk x' hx'I) :=
        hconst (ptOf t) htI ⟨D.trans ha ht₁, ht₃⟩ x' hx'I ⟨ha, hb⟩
      refine ⟨t, ht₁, ht₂, htI, ?_⟩
      show (f.toFun (Subtype.mk (ptOf t) htI)).1 0 = c
      rw [hval]
      rcases hstart with rfl | ⟨hz, hzc⟩
      · rfl
      · exact hzc
    have hE : ∀ y' : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
        ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
          openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
          D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y' := by
      intro y' hy'J
      obtain ⟨a, b, ha, hb, hconst⟩ := hloc hy'J
      refine ⟨a, ha, ?_⟩
      intro s hsJ has hsy hAs
      obtain ⟨hsI, hsc⟩ := hAs
      have hy'I : I y' := hsub hy'J
      have hval : f.toFun (Subtype.mk s hsI) = f.toFun (Subtype.mk y' hy'I) :=
        hconst s hsI ⟨has, D.trans hsy hb⟩ y' hy'I ⟨ha, hb⟩
      exact ⟨hy'I, by rw [← hval]; exact hsc⟩
    have hAy : A y :=
      chain_propagation D u v A (fun z => z = x ∨ A z) F L hL hdich
        (fun z hz => Or.inr hz) hW hE L x y hxJ hyJ hlt (Or.inl rfl) (fun w hw _ _ => hw)
    obtain ⟨hz, hzc⟩ := hAy
    exact hzc.symm
  intro x hxI hxJ y hyI hyJ
  rcases D.trichotomy (x 0) (y 0) with h | h | h
  · exact Subtype.ext (power1_ext (key x y hxJ hyJ h.1 hxI hyI))
  · have : x = y := power1_ext h.1
    subst this
    rfl
  · exact Subtype.ext (power1_ext (key y x hyJ hxJ h.1 hyI hxI)).symm

theorem locally_increasing_implies_increasing (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hloc : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset
      (IncWindowLocus f)) :
    IncOnInterval f u v := by
  intro x hxI hxJ y hyI hyJ hlt
  set c : R := (f.toFun (Subtype.mk x hxI)).1 0 with hc
  set A : Set (Power R 1) :=
    fun z => ∃ hz : I z,
      openInterval D (Endpoint.finite c) Endpoint.posInf ((f.toFun (Subtype.mk z hz)).1) with hAdef
  have hA : M.S 1 A :=
    definable_preimage D M f
      ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval (Endpoint.finite c)
        Endpoint.posInf))
  obtain ⟨F, hFfin, hdich⟩ := definable_interval_dichotomy D ((M.ominimal A).1 hA)
  obtain ⟨L, hL⟩ := hFfin
  have hW : ∀ x' y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → (x' = x ∨ A x') →
      ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t) := by
    intro x' y' hx'J hy'J hlt' hstart
    obtain ⟨a, b, ha, hb, hwsub, hinc⟩ := hloc hx'J
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_between_of_lt D hlt' hb
    have htJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf t) :=
      ⟨D.trans hx'J.1 ht₁, D.trans ht₂ hy'J.2⟩
    have htI : I (ptOf t) := hsub htJ
    have hx'I : I x' := hsub hx'J
    have hstep : D.lt ((f.toFun (Subtype.mk x' hx'I)).1 0) ((f.toFun (Subtype.mk (ptOf t) htI)).1 0) :=
      hinc x' hx'I ⟨ha, hb⟩ (ptOf t) htI ⟨D.trans ha ht₁, ht₃⟩ ht₁
    refine ⟨t, ht₁, ht₂, htI, ?_, trivial⟩
    rcases hstart with rfl | ⟨hz, hzc, -⟩
    · exact hstep
    · exact D.trans hzc hstep
  have hE : ∀ y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
        D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y' := by
    intro y' hy'J
    obtain ⟨a, b, ha, hb, hwsub, hinc⟩ := hloc hy'J
    refine ⟨a, ha, ?_⟩
    intro s hsJ has hsy hAs
    obtain ⟨hsI, hsc, -⟩ := hAs
    have hy'I : I y' := hsub hy'J
    have hstep : D.lt ((f.toFun (Subtype.mk s hsI)).1 0) ((f.toFun (Subtype.mk y' hy'I)).1 0) :=
      hinc s hsI ⟨has, D.trans hsy hb⟩ y' hy'I ⟨ha, hb⟩ hsy
    exact ⟨hy'I, D.trans hsc hstep, trivial⟩
  have hAy : A y :=
    chain_propagation D u v A (fun z => z = x ∨ A z) F L hL hdich
      (fun z hz => Or.inr hz) hW hE L x y hxJ hyJ hlt (Or.inl rfl) (fun w hw _ _ => hw)
  obtain ⟨hz, hzc, -⟩ := hAy
  exact hzc

theorem locally_decreasing_implies_decreasing (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hloc : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset
      (DecWindowLocus f)) :
    DecOnInterval f u v := by
  intro x hxI hxJ y hyI hyJ hlt
  set c : R := (f.toFun (Subtype.mk x hxI)).1 0 with hc
  set A : Set (Power R 1) :=
    fun z => ∃ hz : I z,
      openInterval D Endpoint.negInf (Endpoint.finite c) ((f.toFun (Subtype.mk z hz)).1) with hAdef
  have hA : M.S 1 A :=
    definable_preimage D M f
      ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf
        (Endpoint.finite c)))
  obtain ⟨F, hFfin, hdich⟩ := definable_interval_dichotomy D ((M.ominimal A).1 hA)
  obtain ⟨L, hL⟩ := hFfin
  have hW : ∀ x' y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → (x' = x ∨ A x') →
      ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t) := by
    intro x' y' hx'J hy'J hlt' hstart
    obtain ⟨a, b, ha, hb, hwsub, hdec⟩ := hloc hx'J
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_between_of_lt D hlt' hb
    have htJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf t) :=
      ⟨D.trans hx'J.1 ht₁, D.trans ht₂ hy'J.2⟩
    have htI : I (ptOf t) := hsub htJ
    have hx'I : I x' := hsub hx'J
    have hstep : D.lt ((f.toFun (Subtype.mk (ptOf t) htI)).1 0) ((f.toFun (Subtype.mk x' hx'I)).1 0) :=
      hdec x' hx'I ⟨ha, hb⟩ (ptOf t) htI ⟨D.trans ha ht₁, ht₃⟩ ht₁
    refine ⟨t, ht₁, ht₂, htI, trivial, ?_⟩
    rcases hstart with rfl | ⟨hz, -, hzc⟩
    · exact hstep
    · exact D.trans hstep hzc
  have hE : ∀ y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
        D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y' := by
    intro y' hy'J
    obtain ⟨a, b, ha, hb, hwsub, hdec⟩ := hloc hy'J
    refine ⟨a, ha, ?_⟩
    intro s hsJ has hsy hAs
    obtain ⟨hsI, -, hsc⟩ := hAs
    have hy'I : I y' := hsub hy'J
    have hstep : D.lt ((f.toFun (Subtype.mk y' hy'I)).1 0) ((f.toFun (Subtype.mk s hsI)).1 0) :=
      hdec s hsI ⟨has, D.trans hsy hb⟩ y' hy'I ⟨ha, hb⟩ hsy
    exact ⟨hy'I, trivial, D.trans hstep hsc⟩
  have hAy : A y :=
    chain_propagation D u v A (fun z => z = x ∨ A z) F L hL hdich
      (fun z hz => Or.inr hz) hW hE L x y hxJ hyJ hlt (Or.inl rfl) (fun w hw _ _ => hw)
  obtain ⟨hz, -, hzc⟩ := hAy
  exact hzc

end Instances

end Monotonicity_Theorem


/-! ### UniformGerm -/


namespace Monotonicity_Theorem

section Uniform

variable {R : Type}

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

/-- Local-to-global, increasing case: the below–above germ pattern forces strict increase. -/
theorem increasing_of_uniform_below_above (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hU : UniformBelowAbove D f u v) :
    IncOnInterval f u v := by
  intro x hxI hxJ y hyI hyJ hlt
  set c : R := (f.toFun (Subtype.mk x hxI)).1 0 with hc
  set A : Set (Power R 1) :=
    fun z => ∃ hz : I z,
      openInterval D (Endpoint.finite c) Endpoint.posInf ((f.toFun (Subtype.mk z hz)).1) with hAdef
  have hA : M.S 1 A :=
    definable_preimage D M f
      ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval (Endpoint.finite c)
        Endpoint.posInf))
  obtain ⟨F, hFfin, hdich⟩ := definable_interval_dichotomy D ((M.ominimal A).1 hA)
  obtain ⟨L, hL⟩ := hFfin
  have hW : ∀ x' y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → (x' = x ∨ A x') →
      ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t) := by
    intro x' y' hx'J hy'J hlt' hstart
    have hx'I : I x' := hsub hx'J
    obtain ⟨c₁, c₂, -, hc₂J, -, hxc₂, -, hright⟩ := hU x' hx'I hx'J
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_between_lt3 D hlt' hxc₂
    have htJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf t) :=
      ⟨D.trans hx'J.1 ht₁, D.trans ht₂ hy'J.2⟩
    have htI : I (ptOf t) := hsub htJ
    have hstep :
        D.lt ((f.toFun (Subtype.mk x' hx'I)).1 0) ((f.toFun (Subtype.mk (ptOf t) htI)).1 0) :=
      hright (ptOf t) htI htJ ht₁ ht₃
    refine ⟨t, ht₁, ht₂, htI, ?_, trivial⟩
    rcases hstart with rfl | ⟨hz, hzc, -⟩
    · exact hstep
    · exact D.trans hzc hstep
  have hE : ∀ y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
        D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y' := by
    intro y' hy'J
    have hy'I : I y' := hsub hy'J
    obtain ⟨c₁, c₂, -, -, hc₁y, -, hleft, -⟩ := hU y' hy'I hy'J
    refine ⟨c₁ 0, hc₁y, ?_⟩
    intro s hsJ has hsy hAs
    obtain ⟨hsI, hsc, -⟩ := hAs
    have hstep :
        D.lt ((f.toFun (Subtype.mk s hsI)).1 0) ((f.toFun (Subtype.mk y' hy'I)).1 0) :=
      hleft s hsI hsJ has hsy
    exact ⟨hy'I, D.trans hsc hstep, trivial⟩
  have hAy : A y :=
    chain_propagation D u v A (fun z => z = x ∨ A z) F L hL hdich
      (fun z hz => Or.inr hz) hW hE L x y hxJ hyJ hlt (Or.inl rfl) (fun w hw _ _ => hw)
  obtain ⟨hz, hzc, -⟩ := hAy
  exact hzc

/-- Local-to-global, decreasing case: the above–below germ pattern forces strict decrease. -/
theorem decreasing_of_uniform_above_below (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hU : UniformAboveBelow D f u v) :
    DecOnInterval f u v := by
  intro x hxI hxJ y hyI hyJ hlt
  set c : R := (f.toFun (Subtype.mk x hxI)).1 0 with hc
  set A : Set (Power R 1) :=
    fun z => ∃ hz : I z,
      openInterval D Endpoint.negInf (Endpoint.finite c) ((f.toFun (Subtype.mk z hz)).1) with hAdef
  have hA : M.S 1 A :=
    definable_preimage D M f
      ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf
        (Endpoint.finite c)))
  obtain ⟨F, hFfin, hdich⟩ := definable_interval_dichotomy D ((M.ominimal A).1 hA)
  obtain ⟨L, hL⟩ := hFfin
  have hW : ∀ x' y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → (x' = x ∨ A x') →
      ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t) := by
    intro x' y' hx'J hy'J hlt' hstart
    have hx'I : I x' := hsub hx'J
    obtain ⟨c₁, c₂, -, hc₂J, -, hxc₂, -, hright⟩ := hU x' hx'I hx'J
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_between_lt3 D hlt' hxc₂
    have htJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf t) :=
      ⟨D.trans hx'J.1 ht₁, D.trans ht₂ hy'J.2⟩
    have htI : I (ptOf t) := hsub htJ
    have hstep :
        D.lt ((f.toFun (Subtype.mk (ptOf t) htI)).1 0) ((f.toFun (Subtype.mk x' hx'I)).1 0) :=
      hright (ptOf t) htI htJ ht₁ ht₃
    refine ⟨t, ht₁, ht₂, htI, trivial, ?_⟩
    rcases hstart with rfl | ⟨hz, -, hzc⟩
    · exact hstep
    · exact D.trans hstep hzc
  have hE : ∀ y' : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
        D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y' := by
    intro y' hy'J
    have hy'I : I y' := hsub hy'J
    obtain ⟨c₁, c₂, -, -, hc₁y, -, hleft, -⟩ := hU y' hy'I hy'J
    refine ⟨c₁ 0, hc₁y, ?_⟩
    intro s hsJ has hsy hAs
    obtain ⟨hsI, -, hsc⟩ := hAs
    have hstep :
        D.lt ((f.toFun (Subtype.mk y' hy'I)).1 0) ((f.toFun (Subtype.mk s hsI)).1 0) :=
      hleft s hsI hsJ has hsy
    exact ⟨hy'I, trivial, D.trans hstep hsc⟩
  have hAy : A y :=
    chain_propagation D u v A (fun z => z = x ∨ A z) F L hL hdich
      (fun z hz => Or.inr hz) hW hE L x y hxJ hyJ hlt (Or.inl rfl) (fun w hw _ _ => hw)
  obtain ⟨hz, -, hzc⟩ := hAy
  exact hzc

end Uniform

end Monotonicity_Theorem


/-! ### GermDichotomy -/


namespace Monotonicity_Theorem

variable {R : Type}

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

end Monotonicity_Theorem


/-! ### ConstOrInj -/


namespace Monotonicity_Theorem

section Aux

variable {R : Type}

lemma exists_power3 {P : R → R → R → Prop} :
    (∃ y : Power R 3, P (y 0) (y 1) (y 2)) ↔ ∃ a b c : R, P a b c := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y 0, y 1, y 2, h⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨fun k => if k.val = 0 then a else if k.val = 1 then b else c, h⟩

/-- A union, indexed by a finite list, of finite subsets of the line is finite. -/
lemma isFinite1_list_union :
    ∀ (L : List R) (P : R → Set (Power R 1)), (∀ g ∈ L, IsFinite1 (P g)) →
      IsFinite1 (fun y : Power R 1 => ∃ g, g ∈ L ∧ P g y) := by
  intro L
  induction L with
  | nil =>
      intro P _
      exact ⟨[], fun x => ⟨fun h => absurd h (by rintro ⟨g, hg, -⟩; simp at hg),
        fun h => absurd h (by simp)⟩⟩
  | cons a L ih =>
      intro P hP
      have h1 : IsFinite1 (P a) := hP a (List.mem_cons.2 (Or.inl rfl))
      have h2 : IsFinite1 (fun y : Power R 1 => ∃ g, g ∈ L ∧ P g y) :=
        ih P (fun g hg => hP g (List.mem_cons.2 (Or.inr hg)))
      refine isFinite1_subset (isFinite1_or h1 h2) ?_
      rintro y ⟨g, hg, hy⟩
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact Or.inl hy
      · exact Or.inr ⟨g, hg', hy⟩

end Aux

section Main

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

/-- The fibre of `f` over `c`, intersected with `J`. -/
def FibIn (f : DefinableFunction M I B) (J : Set (Power R 1)) (c : R) : Set (Power R 1) :=
  fun y => J y ∧ ∃ hy : I y, (f.toFun (Subtype.mk y hy)).1 0 = c

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

lemma fibIn_definable (D : DenseLinearOrderNoEndpoints R) (M : OMinimalStructure D)
    (f : DefinableFunction M I B) {J : Set (Power R 1)} (hJ : M.S 1 J) (c : R) :
    M.S 1 (FibIn f J c) := by
  have hpt : M.S 1 (pointSet c) := (M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.point c)
  exact M.inter_mem hJ (definable_preimage D M f hpt)

/-- The set of points of `J` that are not the least point of their own fibre. -/
def NotLeast (f : DefinableFunction M I B) (J : Set (Power R 1)) : Set (Power R 1) :=
  fun x => ∃ z : Power R 1, J z ∧ D.lt (z 0) (x 0) ∧
    ∃ hz : I z, ∃ hx : I x, (f.toFun (Subtype.mk z hz)).1 0 = (f.toFun (Subtype.mk x hx)).1 0

lemma notLeast_definable (D : DenseLinearOrderNoEndpoints R) (M : OMinimalStructure D)
    (f : DefinableFunction M I B) {J : Set (Power R 1)} (hJ : M.S 1 J) :
    M.S 1 (NotLeast f J) := by
  have hBad : M.S 4 (fun t : Power R 4 =>
      (∃ h : I (fun _ => t 0),
        (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      (∃ h : I (fun _ => t 1),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
      J (fun _ => t 1) ∧ D.lt (t 1) (t 0) ∧ t 2 = t 3) :=
    M.inter_mem (defin_graph f 0 2) (M.inter_mem (defin_graph f 1 3)
      (M.inter_mem (defin_at M 1 hJ) (M.inter_mem (defin_lt M 1 0) (defin_eq M 2 3))))
  have hex := M.existsLast_mem (n := 1) (m := 3) hBad
  have hset : (fun x : Power R 1 => ∃ y : Power R 3,
      (fun t : Power R 4 =>
        (∃ h : I (fun _ => t 0),
          (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
        (∃ h : I (fun _ => t 1),
          (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
        J (fun _ => t 1) ∧ D.lt (t 1) (t 0) ∧ t 2 = t 3) (Power.append x y))
      = NotLeast f J := by
    funext x
    apply propext
    constructor
    · intro hh
      obtain ⟨a, b, c, ⟨hx0, hbx⟩, ⟨ha0, hca⟩, hJa, hlt, hbc⟩ :=
        (exists_power3 (P := fun a b c =>
          (∃ h : I (fun _ : Fin 1 => x 0),
            (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => x 0) h)).1) ∧
          (∃ h : I (fun _ : Fin 1 => a),
            (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
          J (fun _ : Fin 1 => a) ∧ D.lt a (x 0) ∧ b = c)).1 hh
      have hxI : I x := by
        have := hx0
        rwa [const_coord x] at this
      refine ⟨pt a, hJa, hlt, ha0, hxI, ?_⟩
      have e1 : c = (f.toFun (Subtype.mk (pt a) ha0)).1 0 := congrFun hca 0
      have e2 : b = (f.toFun (Subtype.mk (pt (x 0)) hx0)).1 0 := congrFun hbx 0
      rw [← e1, ← hbc, e2, fval_pt f x hxI hx0]
    · rintro ⟨z, hJz, hlt, hz, hxI, heq⟩
      refine (exists_power3 (P := fun a b c =>
        (∃ h : I (fun _ : Fin 1 => x 0),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => x 0) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        J (fun _ : Fin 1 => a) ∧ D.lt a (x 0) ∧ b = c)).2 ?_
      refine ⟨z 0, (f.toFun (Subtype.mk x hxI)).1 0, (f.toFun (Subtype.mk z hz)).1 0, ?_, ?_, ?_,
        hlt, heq.symm⟩
      · exact graph_pt f x hxI
      · exact graph_pt f z hz
      · rw [const_coord z]; exact hJz
  rw [hset] at hex
  exact hex

/-- The set of points of `J` that are the least point of their own fibre. -/
def LeastLocus (f : DefinableFunction M I B) (J : Set (Power R 1)) : Set (Power R 1) :=
  fun x => J x ∧ ¬ NotLeast f J x

lemma leastLocus_definable (D : DenseLinearOrderNoEndpoints R) (M : OMinimalStructure D)
    (f : DefinableFunction M I B) {J : Set (Power R 1)} (hJ : M.S 1 J) :
    M.S 1 (LeastLocus f J) :=
  M.inter_mem hJ (M.compl_mem (notLeast_definable D M f hJ))

/-- **Child 1.** On a subinterval, a definable function of one variable is either constant or
injective. -/
theorem constant_or_injective_subinterval (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I) :
    ∃ u₁ v₁ : R, D.lt u₁ v₁ ∧
      (openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) ∧
      (ConstOnInterval f u₁ v₁ ∨
        ∀ x (hx : I x), openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) x →
          ∀ y (hy : I y), openInterval D (Endpoint.finite u₁) (Endpoint.finite v₁) y →
            f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) := by
  classical
  set J : Set (Power R 1) := openInterval D (Endpoint.finite u) (Endpoint.finite v) with hJeq
  have hJ : M.S 1 J := (M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval _ _)
  by_cases hfib : ∃ c : R, ¬ IsFinite1 (FibIn f J c)
  · -- an infinite fibre gives an interval of constancy
    obtain ⟨c, hc⟩ := hfib
    obtain ⟨u₁, v₁, h₁, hsubF⟩ :=
      infinite_contains_interval D ((M.ominimal _).1 (fibIn_definable D M f hJ c)) hc
    refine ⟨u₁, v₁, h₁, fun x hx => (hsubF hx).1, Or.inl ?_⟩
    intro x hx hxJ y hy hyJ
    obtain ⟨-, hx', hxc⟩ := hsubF hxJ
    obtain ⟨-, hy', hyc⟩ := hsubF hyJ
    exact Subtype.ext (power1_ext (by rw [hxc, hyc]))
  · -- all fibres are finite: the least points of the fibres form an infinite definable set
    have hallfin : ∀ c : R, IsFinite1 (FibIn f J c) :=
      fun c => not_not.1 (not_exists.1 hfib c)
    -- every point of `J` lies in the fibre of some least point
    have hleast : ∀ y : Power R 1, J y → ∃ g : R, LeastLocus f J (pt g) ∧
        ∃ hg : I (pt g), FibIn f J ((f.toFun (Subtype.mk (pt g) hg)).1 0) y := by
      intro y hyJ
      have hyI : I y := hsub hyJ
      set c : R := (f.toFun (Subtype.mk y hyI)).1 0 with hc
      obtain ⟨L, hL⟩ := hallfin c
      have hS0 : FibIn f J c (pt (y 0)) := by
        refine ⟨?_, ?_⟩
        · rw [pt_coord y]; exact hyJ
        · refine ⟨by rw [pt_coord y]; exact hyI, ?_⟩
          have he : (Subtype.mk (pt (y 0)) (by rw [pt_coord y]; exact hyI :
              I (pt (y 0))) : {w : Power R 1 // I w}) = Subtype.mk y hyI :=
            Subtype.ext (pt_coord y)
          rw [he]
      obtain ⟨m, hmS, hmin⟩ :=
        exists_least_of_list D L (fun a => FibIn f J c (pt a)) (y 0) hS0
          (fun a ha => (hL (pt a)).1 ha)
      obtain ⟨hmJ, hmI, hmc⟩ := hmS
      refine ⟨m, ⟨hmJ, ?_⟩, hmI, ?_⟩
      · rintro ⟨z, hJz, hlt, hz, hm', heq⟩
        refine hmin (z 0) ⟨?_, ?_⟩ hlt
        · rw [pt_coord z]; exact hJz
        · refine ⟨by rw [pt_coord z]; exact hz, ?_⟩
          have he : (Subtype.mk (pt (z 0)) (by rw [pt_coord z]; exact hz :
              I (pt (z 0))) : {w : Power R 1 // I w}) = Subtype.mk z hz :=
            Subtype.ext (pt_coord z)
          rw [he, heq]
          exact hmc
      · refine ⟨hyJ, hyI, ?_⟩
        rw [hmc]
    -- the least-point locus is infinite
    have hGinf : ¬ IsFinite1 (LeastLocus f J) := by
      rintro ⟨LG, hLG⟩
      refine interval_infinite D huv ?_
      rw [← hJeq]
      refine isFinite1_subset
        (isFinite1_list_union LG
          (fun g => fun y => ∃ hg : I (pt g), FibIn f J ((f.toFun (Subtype.mk (pt g) hg)).1 0) y)
          ?_) ?_
      · intro g _
        by_cases hg : I (pt g)
        · refine isFinite1_subset (hallfin ((f.toFun (Subtype.mk (pt g) hg)).1 0)) ?_
          rintro y ⟨hg', hy⟩
          exact hy
        · exact ⟨[], fun y => ⟨fun h => absurd h.choose hg, fun h => absurd h (by simp)⟩⟩
      · intro y hyJ
        obtain ⟨g, hgL, hg, hfib'⟩ := hleast y hyJ
        exact ⟨g, (hLG (pt g)).1 hgL, hg, hfib'⟩
    obtain ⟨u₁, v₁, h₁, hsubG⟩ :=
      infinite_contains_interval D ((M.ominimal _).1 (leastLocus_definable D M f hJ)) hGinf
    refine ⟨u₁, v₁, h₁, fun x hx => (hsubG hx).1, Or.inr ?_⟩
    intro x hx hxJ y hy hyJ hfxy
    obtain ⟨hxJ', hxnot⟩ := hsubG hxJ
    obtain ⟨hyJ', hynot⟩ := hsubG hyJ
    have hval : (f.toFun (Subtype.mk x hx)).1 0 = (f.toFun (Subtype.mk y hy)).1 0 := by
      rw [hfxy]
    rcases D.trichotomy (x 0) (y 0) with h | h | h
    · exact absurd ⟨x, hxJ', h.1, hx, hy, hval⟩ hynot
    · exact power1_ext h.1
    · exact absurd ⟨y, hyJ', h.1, hy, hx, hval.symm⟩ hxnot

end Main

end Monotonicity_Theorem


/-! ### GermClass -/


namespace Monotonicity_Theorem

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

end Monotonicity_Theorem


/-! ### GermClassMain -/


namespace Monotonicity_Theorem

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


/-! ### VltTools -/


namespace Monotonicity_Theorem

section VltTools

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

open Classical in
/-- The value of `f` at a point of the line, with a junk value off the domain. -/
noncomputable def fv (f : DefinableFunction M I B) (u0 : R) (x : R) : R :=
  if h : I (fun _ : Fin 1 => x) then (f.toFun (Subtype.mk (fun _ : Fin 1 => x) h)).1 0 else u0

lemma fv_eq (f : DefinableFunction M I B) (u0 : R) {x : R} (hx : I (fun _ : Fin 1 => x)) :
    fv f u0 x = (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0 := by
  classical
  simp [fv, hx]

lemma fv_eq' (f : DefinableFunction M I B) (u0 : R) {x : Power R 1} (hx : I x) :
    fv f u0 (x 0) = (f.toFun (Subtype.mk x hx)).1 0 := by
  have hx0 : I (fun _ : Fin 1 => x 0) := mem_eta hx
  rw [fv_eq f u0 hx0, fval_eta f x hx hx0]

variable (Vlt : R → R → Prop)

/-- Points of the domain whose value compares below the value at `x`. -/
def VltLower (f : DefinableFunction M I B) (u0 x : R) : Set (Power R 1) :=
  fun z => I z ∧ Vlt (fv f u0 (z 0)) (fv f u0 x)

lemma vltLower_definable
    (hVdef : ∀ {n : Nat} (i j : Fin n), M.S n (fun t : Power R n => Vlt (t i) (t j)))
    (f : DefinableFunction M I B) (u0 x : R) (hx : I (fun _ : Fin 1 => x)) :
    M.S 1 (VltLower Vlt f u0 x) := by
  have hT : M.S 4 (fun t : Power R 4 =>
      t 1 = x ∧
      (∃ h : I (fun _ => t 1),
        (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
      (∃ h : I (fun _ => t 0),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      Vlt (t 3) (t 2)) :=
    M.inter_mem (defin_const M 1 x)
      (M.inter_mem (defin_graph f 1 2) (M.inter_mem (defin_graph f 0 3) (hVdef 3 2)))
  have hex := M.existsLast_mem (n := 1) (m := 3) hT
  have hset : (fun z : Power R 1 => ∃ y : Power R 3,
      (fun t : Power R 4 =>
        t 1 = x ∧
        (∃ h : I (fun _ => t 1),
          (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
        (∃ h : I (fun _ => t 0),
          (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
        Vlt (t 3) (t 2)) (Power.append z y)) = VltLower Vlt f u0 x := by
    funext z
    apply propext
    constructor
    · intro hy
      obtain ⟨a, b, c, rfl, ⟨hxa, hb⟩, ⟨hz0, hc⟩, hbc⟩ :=
        (exists_power3 (P := fun a b c =>
          a = x ∧
          (∃ h : I (fun _ : Fin 1 => a),
            (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
          (∃ h : I (fun _ : Fin 1 => z 0),
            (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) h)).1) ∧
          Vlt c b)).1 hy
      have hzI : I z := by rw [← const_coord z]; exact hz0
      refine ⟨hzI, ?_⟩
      have hb0 : b = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) hxa)).1 0 := congrFun hb 0
      have hc0 : c = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) hz0)).1 0 := congrFun hc 0
      rw [fv_eq f u0 hxa, fv_eq f u0 hz0, ← hb0, ← hc0]
      exact hbc
    · rintro ⟨hz, hlt⟩
      have hz0 : I (fun _ : Fin 1 => z 0) := mem_eta hz
      refine (exists_power3 (P := fun a b c =>
        a = x ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => z 0),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) h)).1) ∧
        Vlt c b)).2 ?_
      refine ⟨x, (f.toFun (Subtype.mk (fun _ : Fin 1 => x) hx)).1 0,
        (f.toFun (Subtype.mk (fun _ : Fin 1 => z 0) hz0)).1 0, rfl, ⟨hx, power1_ext rfl⟩,
        ⟨hz0, power1_ext rfl⟩, ?_⟩
      rw [fv_eq f u0 hx, fv_eq f u0 hz0] at hlt
      exact hlt
  rw [hset] at hex
  exact hex

/-- The points `x` such that `f` compares above the value at `x` at every domain point `y`
with `Q x y`. -/
def NoBad (f : DefinableFunction M I B) (u0 : R) (Q : R → R → Prop) : Set (Power R 1) :=
  fun x => ¬ ∃ y : R, Q (x 0) y ∧ I (fun _ : Fin 1 => y) ∧ I (fun _ : Fin 1 => x 0) ∧
    ¬ Vlt (fv f u0 (x 0)) (fv f u0 y)

lemma noBad_definable
    (hVdef : ∀ {n : Nat} (i j : Fin n), M.S n (fun t : Power R n => Vlt (t i) (t j)))
    (f : DefinableFunction M I B) (u0 : R) {Q : R → R → Prop}
    (hQ : M.S 2 (fun p : Power R 2 => Q (p 0) (p 1))) :
    M.S 1 (NoBad Vlt f u0 Q) := by
  have hQ4 : M.S 4 (fun t : Power R 4 => Q (t 0) (t 1)) := M.reindex_mem (pair2 0 1) hQ
  have hT : M.S 4 (fun t : Power R 4 =>
      Q (t 0) (t 1) ∧
      (∃ h : I (fun _ => t 0),
        (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      (∃ h : I (fun _ => t 1),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
      ¬ Vlt (t 2) (t 3)) :=
    M.inter_mem hQ4
      (M.inter_mem (defin_graph f 0 2)
        (M.inter_mem (defin_graph f 1 3) (M.compl_mem (hVdef 2 3))))
  have hex := M.existsLast_mem (n := 1) (m := 3) hT
  have hset : setCompl (fun x : Power R 1 => ∃ y : Power R 3,
      (fun t : Power R 4 =>
        Q (t 0) (t 1) ∧
        (∃ h : I (fun _ => t 0),
          (fun _ => t 2 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
        (∃ h : I (fun _ => t 1),
          (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 1) h)).1) ∧
        ¬ Vlt (t 2) (t 3)) (Power.append x y)) = NoBad Vlt f u0 Q := by
    funext x
    apply propext
    constructor
    · intro hno
      intro hbad
      refine hno ?_
      obtain ⟨y, hQxy, hyI, hxI, hnv⟩ := hbad
      refine (exists_power3 (P := fun a b c =>
        Q (x 0) a ∧
        (∃ h : I (fun _ : Fin 1 => x 0),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => x 0) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        ¬ Vlt b c)).2 ?_
      refine ⟨y, (f.toFun (Subtype.mk (fun _ : Fin 1 => x 0) hxI)).1 0,
        (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hyI)).1 0, hQxy, ⟨hxI, power1_ext rfl⟩,
        ⟨hyI, power1_ext rfl⟩, ?_⟩
      rw [fv_eq f u0 hxI, fv_eq f u0 hyI] at hnv
      exact hnv
    · intro hnb hex2
      obtain ⟨a, b, c, hQ0, ⟨hxI, hb⟩, ⟨hyI, hc⟩, hnv⟩ :=
        (exists_power3 (P := fun a b c =>
          Q (x 0) a ∧
          (∃ h : I (fun _ : Fin 1 => x 0),
            (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => x 0) h)).1) ∧
          (∃ h : I (fun _ : Fin 1 => a),
            (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
          ¬ Vlt b c)).1 hex2
      refine hnb ⟨a, hQ0, hyI, hxI, ?_⟩
      have hb0 : b = (f.toFun (Subtype.mk (fun _ : Fin 1 => x 0) hxI)).1 0 := congrFun hb 0
      have hc0 : c = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) hyI)).1 0 := congrFun hc 0
      rw [fv_eq f u0 hxI, fv_eq f u0 hyI, ← hb0, ← hc0]
      exact hnv
  have hc := M.compl_mem hex
  rw [hset] at hc
  exact hc

/-- Comparison with a constant on the left is definable. -/
lemma defin_const_lt {n : Nat} (M : OMinimalStructure D) (i : Fin n) (c : R) :
    M.S n (fun t : Power R n => D.lt c (t i)) := by
  have h : M.S n (fun t : Power R n =>
      openInterval D (Endpoint.finite c) Endpoint.posInf (fun _ => t i)) :=
    defin_at M i ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval _ _))
  have hset : (fun t : Power R n =>
      openInterval D (Endpoint.finite c) Endpoint.posInf (fun _ => t i))
      = (fun t : Power R n => D.lt c (t i)) := by
    funext t
    exact propext ⟨fun hx => hx.1, fun hx => ⟨hx, trivial⟩⟩
  rw [hset] at h
  exact h

/-- Comparison with a constant on the right is definable. -/
lemma defin_lt_const {n : Nat} (M : OMinimalStructure D) (i : Fin n) (c : R) :
    M.S n (fun t : Power R n => D.lt (t i) c) := by
  have h : M.S n (fun t : Power R n =>
      openInterval D Endpoint.negInf (Endpoint.finite c) (fun _ => t i)) :=
    defin_at M i ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.interval _ _))
  have hset : (fun t : Power R n =>
      openInterval D Endpoint.negInf (Endpoint.finite c) (fun _ => t i))
      = (fun t : Power R n => D.lt (t i) c) := by
    funext t
    exact propext ⟨fun hx => hx.2, fun hx => ⟨trivial, hx⟩⟩
  rw [hset] at h
  exact h

/-- Two-parameter version of `NoBad`. -/
def NoBad2 (f : DefinableFunction M I B) (u0 : R) (Q : R → R → R → Prop) : Set (Power R 2) :=
  fun s => ¬ ∃ y : R, Q (s 0) (s 1) y ∧ I (fun _ : Fin 1 => y) ∧ I (fun _ : Fin 1 => s 0) ∧
    ¬ Vlt (fv f u0 (s 0)) (fv f u0 y)

lemma noBad2_definable
    (hVdef : ∀ {n : Nat} (i j : Fin n), M.S n (fun t : Power R n => Vlt (t i) (t j)))
    (f : DefinableFunction M I B) (u0 : R) {Q : R → R → R → Prop}
    (hQ : M.S 3 (fun t : Power R 3 => Q (t 0) (t 1) (t 2))) :
    M.S 2 (NoBad2 Vlt f u0 Q) := by
  have hQ5 : M.S 5 (fun t : Power R 5 => Q (t 0) (t 1) (t 2)) :=
    M.reindex_mem (fun k : Fin 3 => (⟨k.val, by omega⟩ : Fin 5)) hQ
  have hT : M.S 5 (fun t : Power R 5 =>
      Q (t 0) (t 1) (t 2) ∧
      (∃ h : I (fun _ => t 0),
        (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
      (∃ h : I (fun _ => t 2),
        (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
      ¬ Vlt (t 3) (t 4)) :=
    M.inter_mem hQ5
      (M.inter_mem (defin_graph f 0 3)
        (M.inter_mem (defin_graph f 2 4) (M.compl_mem (hVdef 3 4))))
  have hex := M.existsLast_mem (n := 2) (m := 3) hT
  have hset : setCompl (fun s : Power R 2 => ∃ y : Power R 3,
      (fun t : Power R 5 =>
        Q (t 0) (t 1) (t 2) ∧
        (∃ h : I (fun _ => t 0),
          (fun _ => t 3 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 0) h)).1) ∧
        (∃ h : I (fun _ => t 2),
          (fun _ => t 4 : Power R 1) = (f.toFun (Subtype.mk (fun _ => t 2) h)).1) ∧
        ¬ Vlt (t 3) (t 4)) (Power.append s y)) = NoBad2 Vlt f u0 Q := by
    funext s
    apply propext
    constructor
    · intro hno hbad
      refine hno ?_
      obtain ⟨y, hQxy, hyI, hxI, hnv⟩ := hbad
      refine (exists_power3 (P := fun a b c =>
        Q (s 0) (s 1) a ∧
        (∃ h : I (fun _ : Fin 1 => s 0),
          (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => s 0) h)).1) ∧
        (∃ h : I (fun _ : Fin 1 => a),
          (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
        ¬ Vlt b c)).2 ?_
      refine ⟨y, (f.toFun (Subtype.mk (fun _ : Fin 1 => s 0) hxI)).1 0,
        (f.toFun (Subtype.mk (fun _ : Fin 1 => y) hyI)).1 0, hQxy, ⟨hxI, power1_ext rfl⟩,
        ⟨hyI, power1_ext rfl⟩, ?_⟩
      rw [fv_eq f u0 hxI, fv_eq f u0 hyI] at hnv
      exact hnv
    · intro hnb hex2
      obtain ⟨a, b, c, hQ0, ⟨hxI, hb⟩, ⟨hyI, hc⟩, hnv⟩ :=
        (exists_power3 (P := fun a b c =>
          Q (s 0) (s 1) a ∧
          (∃ h : I (fun _ : Fin 1 => s 0),
            (fun _ : Fin 1 => b) = (f.toFun (Subtype.mk (fun _ : Fin 1 => s 0) h)).1) ∧
          (∃ h : I (fun _ : Fin 1 => a),
            (fun _ : Fin 1 => c) = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) h)).1) ∧
          ¬ Vlt b c)).1 hex2
      refine hnb ⟨a, hQ0, hyI, hxI, ?_⟩
      have hb0 : b = (f.toFun (Subtype.mk (fun _ : Fin 1 => s 0) hxI)).1 0 := congrFun hb 0
      have hc0 : c = (f.toFun (Subtype.mk (fun _ : Fin 1 => a) hyI)).1 0 := congrFun hc 0
      rw [fv_eq f u0 hxI, fv_eq f u0 hyI, ← hb0, ← hc0]
      exact hnv
  have hc := M.compl_mem hex
  rw [hset] at hc
  exact hc

end VltTools

end Monotonicity_Theorem


/-! ### NoExtremum -/


namespace Monotonicity_Theorem

section NoExtremum

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

/-- The hypotheses of the "no interval of strict local extrema" theorem, in a form referring
only to points of the line.  `Vlt` is the comparison used on values: taking it to be the order
gives strict local minima, taking it to be the reversed order gives strict local maxima. -/
structure LocalExtCtx (D : DenseLinearOrderNoEndpoints R) (M : OMinimalStructure D)
    {I B : Set (Power R 1)} (Vlt : R → R → Prop) (f : DefinableFunction M I B) (u v : R) :
    Prop where
  Virr : ∀ a : R, ¬ Vlt a a
  Vtr : ∀ {a b c : R}, Vlt a b → Vlt b c → Vlt a c
  Vtri : ∀ a b : R, a = b ∨ Vlt a b ∨ Vlt b a
  Vdef : ∀ {n : Nat} (i j : Fin n), M.S n (fun t : Power R n => Vlt (t i) (t j))
  uv : D.lt u v
  sub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I
  loc : ∀ x : R, D.lt u x → D.lt x v →
    ∃ c₁ c₂ : R, D.lt u c₁ ∧ D.lt c₁ x ∧ D.lt x c₂ ∧ D.lt c₂ v ∧
      ∀ y : R, D.lt c₁ y → D.lt y c₂ → ¬ (y = x) → Vlt (fv f u x) (fv f u y)
  inj : ∀ x y : R, D.lt u x → D.lt x v → D.lt u y → D.lt y v →
    fv f u x = fv f u y → x = y

variable {Vlt : R → R → Prop} {f : DefinableFunction M I B} {u v : R}

lemma LocalExtCtx.mem (C : LocalExtCtx D M Vlt f u v) {x : R}
    (h1 : D.lt u x) (h2 : D.lt x v) : I (fun _ : Fin 1 => x) :=
  C.sub (show openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ : Fin 1 => x)
    from ⟨h1, h2⟩)

/-- Distinct points of the interval have comparable, distinct values. -/
lemma LocalExtCtx.cmp (C : LocalExtCtx D M Vlt f u v) {x y : R}
    (hx1 : D.lt u x) (hx2 : D.lt x v) (hy1 : D.lt u y) (hy2 : D.lt y v) (hne : ¬ (x = y)) :
    Vlt (fv f u x) (fv f u y) ∨ Vlt (fv f u y) (fv f u x) := by
  rcases C.Vtri (fv f u x) (fv f u y) with he | h | h
  · exact absurd (C.inj x y hx1 hx2 hy1 hy2 he) hne
  · exact Or.inl h
  · exact Or.inr h

/-- If the value does not drop, it rises. -/
lemma LocalExtCtx.not_lt (C : LocalExtCtx D M Vlt f u v) {x y : R}
    (hx1 : D.lt u x) (hx2 : D.lt x v) (hy1 : D.lt u y) (hy2 : D.lt y v) (hne : ¬ (x = y))
    (h : ¬ Vlt (fv f u y) (fv f u x)) : Vlt (fv f u x) (fv f u y) := by
  rcases C.cmp hx1 hx2 hy1 hy2 hne with h1 | h1
  · exact h1
  · exact absurd h1 h

/-- The first point to the right of `x`, before `q`, at which the value drops below the value
at `x`. -/
lemma first_descent (C : LocalExtCtx D M Vlt f u v) {x q : R}
    (hux : D.lt u x) (hxq : D.lt x q) (hqv : ¬ D.lt v q)
    (hne : ∃ y : R, D.lt x y ∧ D.lt y q ∧ Vlt (fv f u y) (fv f u x)) :
    ∃ z : R, D.lt x z ∧ D.lt z q ∧ Vlt (fv f u z) (fv f u x) ∧
      ∀ w : R, D.lt x w → D.lt w z → ¬ Vlt (fv f u w) (fv f u x) := by
  have hqv' : ∀ {t : R}, D.lt t q → D.lt t v := by
    intro t ht
    rcases D.trichotomy q v with h | h | h
    · exact D.trans ht h.1
    · exact h.1 ▸ ht
    · exact absurd h.1 hqv
  have hxv : D.lt x v := hqv' hxq
  have hxI : I (fun _ : Fin 1 => x) := C.mem hux hxv
  have hAd : M.S 1 (fun w : Power R 1 =>
      (D.lt x (w 0) ∧ D.lt (w 0) q) ∧ VltLower Vlt f u x w) :=
    M.inter_mem (M.inter_mem (defin_const_lt M 0 x) (defin_lt_const M 0 q))
      (vltLower_definable Vlt C.Vdef f u x hxI)
  have hAf : FiniteUnionOfPointsAndIntervals D
      (fun w : Power R 1 => (D.lt x (w 0) ∧ D.lt (w 0) q) ∧ VltLower Vlt f u x w) :=
    (M.ominimal _).1 hAd
  have hAmem : ∀ w : R, D.lt x w → D.lt w q →
      (((D.lt x w ∧ D.lt w q) ∧ VltLower Vlt f u x (pt w)) ↔ Vlt (fv f u w) (fv f u x)) := by
    intro w h1 h2
    constructor
    · rintro ⟨-, -, hlt⟩
      exact hlt
    · intro hlt
      exact ⟨⟨h1, h2⟩, C.mem (D.trans hux h1) (hqv' h2), hlt⟩
  obtain ⟨y0, hxy0, hy0q, hv0⟩ := hne
  obtain ⟨z, hzx, hlb, hcase⟩ :=
    exists_inf_of_definable D hAf x ⟨y0, hxy0, (hAmem y0 hxy0 hy0q).2 hv0⟩
  have hzA : (D.lt x z ∧ D.lt z q) ∧ VltLower Vlt f u x (pt z) := by
    rcases hcase with h | ⟨w0, hzw0, hall⟩
    · exact h
    · obtain ⟨t0, ht01, ht02⟩ := D.dense hzw0
      have ht0A := hall t0 ht01 ht02
      have hzq : D.lt z q := D.trans ht01 ht0A.1.2
      have hxz : D.lt x z := by
        rcases D.trichotomy x z with h | h | h
        · exact h.1
        · exfalso
          obtain ⟨c₁, c₂, hc1u, hc1x, hxc2, hc2v, hwin⟩ := C.loc x hux hxv
          have hzc2 : D.lt z c₂ := by rw [← h.1]; exact hxc2
          obtain ⟨t, htz, htw, htc⟩ := exists_between_lt3 D hzw0 hzc2
          have htA := hall t htz htw
          have h1 : Vlt (fv f u t) (fv f u x) := htA.2.2
          have hxt : D.lt x t := by rw [h.1]; exact htz
          have h2 : Vlt (fv f u x) (fv f u t) :=
            hwin t (D.trans hc1x hxt) htc (fun he => D.irrefl x (by rw [he] at hxt; exact hxt))
          exact C.Virr _ (C.Vtr h2 h1)
        · exact absurd h.1 hzx
      have huz : D.lt u z := D.trans hux hxz
      have hzv : D.lt z v := hqv' hzq
      obtain ⟨d₁, d₂, hd1u, hd1z, hzd2, hd2v, hwin⟩ := C.loc z huz hzv
      obtain ⟨t, htz, htw, htd⟩ := exists_between_lt3 D hzw0 hzd2
      have htA := hall t htz htw
      have h1 : Vlt (fv f u t) (fv f u x) := htA.2.2
      have h2 : Vlt (fv f u z) (fv f u t) :=
        hwin t (D.trans hd1z htz) htd (fun he => D.irrefl z (by rw [he] at htz; exact htz))
      exact (hAmem z hxz hzq).2 (C.Vtr h2 h1)
  refine ⟨z, hzA.1.1, hzA.1.2, hzA.2.2, ?_⟩
  intro w hxw hwz hvw
  exact hlb w hxw ((hAmem w hxw (D.trans hwz hzA.1.2)).2 hvw) hwz

/-- The last point to the left of `x`, after `p`, at which the value drops below the value
at `x`. -/
lemma last_descent (C : LocalExtCtx D M Vlt f u v) {x p : R}
    (hxv : D.lt x v) (hpx : D.lt p x) (hpu : ¬ D.lt p u)
    (hne : ∃ y : R, D.lt p y ∧ D.lt y x ∧ Vlt (fv f u y) (fv f u x)) :
    ∃ z : R, D.lt p z ∧ D.lt z x ∧ Vlt (fv f u z) (fv f u x) ∧
      ∀ w : R, D.lt z w → D.lt w x → ¬ Vlt (fv f u w) (fv f u x) := by
  have hpu' : ∀ {t : R}, D.lt p t → D.lt u t := by
    intro t ht
    rcases D.trichotomy p u with h | h | h
    · exact absurd h.1 hpu
    · exact h.1 ▸ ht
    · exact D.trans h.1 ht
  have hux : D.lt u x := hpu' hpx
  have hxI : I (fun _ : Fin 1 => x) := C.mem hux hxv
  have hAd : M.S 1 (fun w : Power R 1 =>
      (D.lt p (w 0) ∧ D.lt (w 0) x) ∧ VltLower Vlt f u x w) :=
    M.inter_mem (M.inter_mem (defin_const_lt M 0 p) (defin_lt_const M 0 x))
      (vltLower_definable Vlt C.Vdef f u x hxI)
  have hAf : FiniteUnionOfPointsAndIntervals D
      (fun w : Power R 1 => (D.lt p (w 0) ∧ D.lt (w 0) x) ∧ VltLower Vlt f u x w) :=
    (M.ominimal _).1 hAd
  have hAmem : ∀ w : R, D.lt p w → D.lt w x →
      (((D.lt p w ∧ D.lt w x) ∧ VltLower Vlt f u x (pt w)) ↔ Vlt (fv f u w) (fv f u x)) := by
    intro w h1 h2
    constructor
    · rintro ⟨-, -, hlt⟩
      exact hlt
    · intro hlt
      exact ⟨⟨h1, h2⟩, C.mem (hpu' h1) (D.trans h2 hxv), hlt⟩
  obtain ⟨y0, hpy0, hy0x, hv0⟩ := hne
  obtain ⟨z, hxz, hub, hcase⟩ :=
    exists_sup_of_definable D hAf x ⟨y0, hy0x, (hAmem y0 hpy0 hy0x).2 hv0⟩
  have hzA : (D.lt p z ∧ D.lt z x) ∧ VltLower Vlt f u x (pt z) := by
    rcases hcase with h | ⟨w0, hw0z, hall⟩
    · exact h
    · obtain ⟨t0, ht01, ht02⟩ := D.dense hw0z
      have ht0A := hall t0 ht02 ht01
      have hpz : D.lt p z := D.trans ht0A.1.1 ht02
      have hzx : D.lt z x := by
        rcases D.trichotomy z x with h | h | h
        · exact h.1
        · exfalso
          obtain ⟨c₁, c₂, hc1u, hc1x, hxc2, hc2v, hwin⟩ := C.loc x hux hxv
          have hc1z : D.lt c₁ z := by rw [h.1]; exact hc1x
          obtain ⟨t, htz, hwt, hct⟩ := exists_between_gt3 D hw0z hc1z
          have htA := hall t htz hwt
          have h1 : Vlt (fv f u t) (fv f u x) := htA.2.2
          have htx : D.lt t x := by rw [← h.1]; exact htz
          have h2 : Vlt (fv f u x) (fv f u t) :=
            hwin t hct (D.trans htx hxc2) (fun he => D.irrefl x (by rw [he] at htx; exact htx))
          exact C.Virr _ (C.Vtr h2 h1)
        · exact absurd h.1 hxz
      have huz : D.lt u z := hpu' hpz
      have hzv : D.lt z v := D.trans hzx hxv
      obtain ⟨d₁, d₂, hd1u, hd1z, hzd2, hd2v, hwin⟩ := C.loc z huz hzv
      obtain ⟨t, htz, hwt, hdt⟩ := exists_between_gt3 D hw0z hd1z
      have htA := hall t htz hwt
      have h1 : Vlt (fv f u t) (fv f u x) := htA.2.2
      have h2 : Vlt (fv f u z) (fv f u t) :=
        hwin t hdt (D.trans htz hzd2) (fun he => D.irrefl z (by rw [he] at htz; exact htz))
      exact (hAmem z hpz hzx).2 (C.Vtr h2 h1)
  exact ⟨z, hzA.1.1, hzA.1.2, hzA.2.2, fun w hzw hwx hvw =>
    hub w hwx ((hAmem w (D.trans hzA.1.1 hzw) hwx).2 hvw) hzw⟩

/-- The minimum of `f` on `[c,q)`. -/
lemma min_right (C : LocalExtCtx D M Vlt f u v) {c q : R}
    (huc : D.lt u c) (hcq : D.lt c q) (hqv : ¬ D.lt v q) :
    ∃ m : R, ¬ D.lt m c ∧ D.lt m q ∧
      ∀ y : R, ¬ D.lt y c → D.lt y q → ¬ (y = m) → Vlt (fv f u m) (fv f u y) := by
  have hqv' : ∀ {t : R}, D.lt t q → D.lt t v := by
    intro t ht
    rcases D.trichotomy q v with h | h | h
    · exact D.trans ht h.1
    · exact h.1 ▸ ht
    · exact absurd h.1 hqv
  have hmemI : ∀ t : R, ¬ D.lt t c → D.lt t q → D.lt u t ∧ D.lt t v := by
    intro t h1 h2
    refine ⟨?_, hqv' h2⟩
    rcases D.trichotomy t c with h | h | h
    · exact absurd h.1 h1
    · exact h.1 ▸ huc
    · exact D.trans huc h.1
  have hge : ∀ {m z : R}, ¬ D.lt m c → D.lt m z → ¬ D.lt z c := by
    intro m z hmc hmz hzc
    rcases D.trichotomy m c with h | h | h
    · exact hmc h.1
    · exact D.irrefl m (D.trans hmz (by rw [h.1]; exact hzc))
    · exact D.irrefl m (D.trans hmz (D.trans hzc h.1))
  have hQdef : M.S 2 (fun p : Power R 2 => ¬ D.lt (p 1) c ∧ D.lt (p 1) (p 0)) :=
    M.inter_mem (M.compl_mem (defin_lt_const M 1 c)) (defin_lt M 1 0)
  have hCd : M.S 1 (fun x : Power R 1 =>
      (¬ D.lt (x 0) c ∧ D.lt (x 0) q) ∧
        NoBad Vlt f u (fun a b => ¬ D.lt b c ∧ D.lt b a) x) :=
    M.inter_mem (M.inter_mem (M.compl_mem (defin_lt_const M 0 c)) (defin_lt_const M 0 q))
      (noBad_definable Vlt C.Vdef f u hQdef)
  have hmem : ∀ x : R, ¬ D.lt x c → D.lt x q →
      (((¬ D.lt x c ∧ D.lt x q) ∧
          NoBad Vlt f u (fun a b => ¬ D.lt b c ∧ D.lt b a) (pt x))
        ↔ ∀ y : R, ¬ D.lt y c → D.lt y x → Vlt (fv f u x) (fv f u y)) := by
    intro x h1 h2
    constructor
    · rintro ⟨-, hnb⟩ y hy1 hy2
      by_contra hv
      obtain ⟨hyu, hyv⟩ := hmemI y hy1 (D.trans hy2 h2)
      obtain ⟨hxu, hxv⟩ := hmemI x h1 h2
      exact hnb ⟨y, ⟨hy1, hy2⟩, C.mem hyu hyv, C.mem hxu hxv, hv⟩
    · intro hall
      refine ⟨⟨h1, h2⟩, ?_⟩
      rintro ⟨y, ⟨hy1, hy2⟩, -, -, hv⟩
      exact hv (hall y hy1 hy2)
  have hcC : ((¬ D.lt c c ∧ D.lt c q) ∧
      NoBad Vlt f u (fun a b => ¬ D.lt b c ∧ D.lt b a) (pt c)) := by
    refine (hmem c (D.irrefl c) hcq).2 ?_
    intro y hy1 hy2
    exact absurd hy2 hy1
  have hno : ∀ p1 q1 : R, D.lt p1 q1 →
      ¬ (openInterval D (Endpoint.finite p1) (Endpoint.finite q1)).Subset
        (fun x : Power R 1 => (¬ D.lt (x 0) c ∧ D.lt (x 0) q) ∧
          NoBad Vlt f u (fun a b => ¬ D.lt b c ∧ D.lt b a) x) := by
    intro p1 q1 h12 hsub1
    obtain ⟨x, hx1, hx2⟩ := D.dense h12
    have hxC := hsub1 (show openInterval D (Endpoint.finite p1) (Endpoint.finite q1) (pt x)
      from ⟨hx1, hx2⟩)
    obtain ⟨hux, hxv⟩ := hmemI x hxC.1.1 hxC.1.2
    obtain ⟨d₁, d₂, -, hd1x, hxd2, -, hwin⟩ := C.loc x hux hxv
    obtain ⟨t, hxt, htd2, htq1⟩ := exists_between_lt3 D hxd2 hx2
    have htC := hsub1 (show openInterval D (Endpoint.finite p1) (Endpoint.finite q1) (pt t)
      from ⟨D.trans hx1 hxt, htq1⟩)
    have h1 : Vlt (fv f u t) (fv f u x) :=
      ((hmem t htC.1.1 htC.1.2).1 htC) x hxC.1.1 hxt
    have h2 : Vlt (fv f u x) (fv f u t) :=
      hwin t (D.trans hd1x hxt) htd2 (fun he => D.irrefl x (by rw [he] at hxt; exact hxt))
    exact C.Virr _ (C.Vtr h2 h1)
  have hfin : IsFinite1 (fun x : Power R 1 => (¬ D.lt (x 0) c ∧ D.lt (x 0) q) ∧
      NoBad Vlt f u (fun a b => ¬ D.lt b c ∧ D.lt b a) x) :=
    isFinite1_of_no_interval D ((M.ominimal _).1 hCd) hno
  obtain ⟨m, hmC, hmax⟩ := exists_greatest_of_finite D hfin hcC
  refine ⟨m, hmC.1.1, hmC.1.2, ?_⟩
  intro y hyc hyq hne
  by_contra hnv
  obtain ⟨hmu, hmv⟩ := hmemI m hmC.1.1 hmC.1.2
  obtain ⟨hyu, hyv⟩ := hmemI y hyc hyq
  have hylt : Vlt (fv f u y) (fv f u m) := C.not_lt hyu hyv hmu hmv hne hnv
  rcases D.trichotomy y m with h | h | h
  · exact C.Virr _ (C.Vtr hylt (((hmem m hmC.1.1 hmC.1.2).1 hmC) y hyc h.1))
  · exact hne h.1
  · obtain ⟨z, hmz, hzq, hvz, hmin⟩ :=
      first_descent C hmu hmC.1.2 hqv ⟨y, h.1, hyq, hylt⟩
    have hzc : ¬ D.lt z c := hge hmC.1.1 hmz
    have hzC : ((¬ D.lt z c ∧ D.lt z q) ∧
        NoBad Vlt f u (fun a b => ¬ D.lt b c ∧ D.lt b a) (pt z)) := by
      refine (hmem z hzc hzq).2 ?_
      intro t htc htz
      obtain ⟨htu, htv⟩ := hmemI t htc (D.trans htz hzq)
      rcases D.trichotomy t m with h1 | h1 | h1
      · exact C.Vtr hvz (((hmem m hmC.1.1 hmC.1.2).1 hmC) t htc h1.1)
      · rw [h1.1]; exact hvz
      · have hnotlt : ¬ Vlt (fv f u t) (fv f u m) := hmin t h1.1 htz
        exact C.Vtr hvz (C.not_lt hmu hmv htu htv
          (fun he => D.irrefl t (by rw [he] at h1; exact h1.1)) hnotlt)
    exact hmax z hzC hmz

/-- The minimum of `f` on `(u,c]`. -/
lemma min_left (C : LocalExtCtx D M Vlt f u v) {c : R}
    (huc : D.lt u c) (hcv : D.lt c v) :
    ∃ m : R, D.lt u m ∧ ¬ D.lt c m ∧
      ∀ y : R, D.lt u y → ¬ D.lt c y → ¬ (y = m) → Vlt (fv f u m) (fv f u y) := by
  have hmemI : ∀ t : R, D.lt u t → ¬ D.lt c t → D.lt u t ∧ D.lt t v := by
    intro t h1 h2
    refine ⟨h1, ?_⟩
    rcases D.trichotomy t c with h | h | h
    · exact D.trans h.1 hcv
    · exact h.1 ▸ hcv
    · exact absurd h.1 h2
  have hle : ∀ {m z : R}, ¬ D.lt c m → D.lt z m → ¬ D.lt c z := by
    intro m z hcm hzm hcz
    rcases D.trichotomy c m with h | h | h
    · exact hcm h.1
    · exact D.irrefl m (D.trans (by rw [← h.1]; exact hcz) hzm)
    · exact D.irrefl m (D.trans (D.trans h.1 hcz) hzm)
  have hQdef : M.S 2 (fun p : Power R 2 => ¬ D.lt c (p 1) ∧ D.lt (p 0) (p 1)) :=
    M.inter_mem (M.compl_mem (defin_const_lt M 1 c)) (defin_lt M 0 1)
  have hCd : M.S 1 (fun x : Power R 1 =>
      (D.lt u (x 0) ∧ ¬ D.lt c (x 0)) ∧
        NoBad Vlt f u (fun a b => ¬ D.lt c b ∧ D.lt a b) x) :=
    M.inter_mem (M.inter_mem (defin_const_lt M 0 u) (M.compl_mem (defin_const_lt M 0 c)))
      (noBad_definable Vlt C.Vdef f u hQdef)
  have hmem : ∀ x : R, D.lt u x → ¬ D.lt c x →
      (((D.lt u x ∧ ¬ D.lt c x) ∧
          NoBad Vlt f u (fun a b => ¬ D.lt c b ∧ D.lt a b) (pt x))
        ↔ ∀ y : R, ¬ D.lt c y → D.lt x y → Vlt (fv f u x) (fv f u y)) := by
    intro x h1 h2
    constructor
    · rintro ⟨-, hnb⟩ y hy1 hy2
      by_contra hv
      obtain ⟨hyu, hyv⟩ := hmemI y (D.trans h1 hy2) hy1
      obtain ⟨hxu, hxv⟩ := hmemI x h1 h2
      exact hnb ⟨y, ⟨hy1, hy2⟩, C.mem hyu hyv, C.mem hxu hxv, hv⟩
    · intro hall
      refine ⟨⟨h1, h2⟩, ?_⟩
      rintro ⟨y, ⟨hy1, hy2⟩, -, -, hv⟩
      exact hv (hall y hy1 hy2)
  have hcC : ((D.lt u c ∧ ¬ D.lt c c) ∧
      NoBad Vlt f u (fun a b => ¬ D.lt c b ∧ D.lt a b) (pt c)) := by
    refine (hmem c huc (D.irrefl c)).2 ?_
    intro y hy1 hy2
    exact absurd hy2 hy1
  have hno : ∀ p1 q1 : R, D.lt p1 q1 →
      ¬ (openInterval D (Endpoint.finite p1) (Endpoint.finite q1)).Subset
        (fun x : Power R 1 => (D.lt u (x 0) ∧ ¬ D.lt c (x 0)) ∧
          NoBad Vlt f u (fun a b => ¬ D.lt c b ∧ D.lt a b) x) := by
    intro p1 q1 h12 hsub1
    obtain ⟨x, hx1, hx2⟩ := D.dense h12
    have hxC := hsub1 (show openInterval D (Endpoint.finite p1) (Endpoint.finite q1) (pt x)
      from ⟨hx1, hx2⟩)
    obtain ⟨hux, hxv⟩ := hmemI x hxC.1.1 hxC.1.2
    obtain ⟨d₁, d₂, -, hd1x, hxd2, -, hwin⟩ := C.loc x hux hxv
    obtain ⟨t, htx, hp1t, hd1t⟩ := exists_between_gt3 D hx1 hd1x
    have htC := hsub1 (show openInterval D (Endpoint.finite p1) (Endpoint.finite q1) (pt t)
      from ⟨hp1t, D.trans htx hx2⟩)
    have h1 : Vlt (fv f u t) (fv f u x) :=
      ((hmem t htC.1.1 htC.1.2).1 htC) x hxC.1.2 htx
    have h2 : Vlt (fv f u x) (fv f u t) :=
      hwin t hd1t (D.trans htx hxd2) (fun he => D.irrefl x (by rw [he] at htx; exact htx))
    exact C.Virr _ (C.Vtr h2 h1)
  have hfin : IsFinite1 (fun x : Power R 1 => (D.lt u (x 0) ∧ ¬ D.lt c (x 0)) ∧
      NoBad Vlt f u (fun a b => ¬ D.lt c b ∧ D.lt a b) x) :=
    isFinite1_of_no_interval D ((M.ominimal _).1 hCd) hno
  obtain ⟨m, hmC, hmin0⟩ := exists_least_of_finite D hfin hcC
  refine ⟨m, hmC.1.1, hmC.1.2, ?_⟩
  intro y hyu hyc hne
  by_contra hnv
  obtain ⟨hmu, hmv⟩ := hmemI m hmC.1.1 hmC.1.2
  obtain ⟨hyu', hyv⟩ := hmemI y hyu hyc
  have hylt : Vlt (fv f u y) (fv f u m) := C.not_lt hyu' hyv hmu hmv hne hnv
  rcases D.trichotomy y m with h | h | h
  · obtain ⟨z, huz, hzm, hvz, hlast⟩ :=
      last_descent C hmv hmC.1.1 (D.irrefl u) ⟨y, hyu, h.1, hylt⟩
    have hzc : ¬ D.lt c z := hle hmC.1.2 hzm
    have hzC : ((D.lt u z ∧ ¬ D.lt c z) ∧
        NoBad Vlt f u (fun a b => ¬ D.lt c b ∧ D.lt a b) (pt z)) := by
      refine (hmem z huz hzc).2 ?_
      intro t htc hzt
      obtain ⟨htu, htv⟩ := hmemI t (D.trans huz hzt) htc
      rcases D.trichotomy m t with h1 | h1 | h1
      · exact C.Vtr hvz (((hmem m hmC.1.1 hmC.1.2).1 hmC) t htc h1.1)
      · rw [← h1.1]; exact hvz
      · have hnotlt : ¬ Vlt (fv f u t) (fv f u m) := hlast t hzt h1.1
        exact C.Vtr hvz (C.not_lt hmu hmv htu htv
          (fun he => D.irrefl t (by rw [he] at h1; exact h1.1)) hnotlt)
    exact hmin0 z hzC hzm
  · exact hne h.1
  · exact C.Virr _ (C.Vtr hylt (((hmem m hmC.1.1 hmC.1.2).1 hmC) y hyc h.1))

/-- The minimum of `f` on `(u,q)`. -/
lemma min_interval (C : LocalExtCtx D M Vlt f u v) {q : R}
    (huq : D.lt u q) (hqv : ¬ D.lt v q) :
    ∃ m : R, D.lt u m ∧ D.lt m q ∧
      ∀ y : R, D.lt u y → D.lt y q → ¬ (y = m) → Vlt (fv f u m) (fv f u y) := by
  have hasym : ∀ {a b : R}, D.lt a b → ¬ D.lt b a := fun h h' => D.irrefl _ (D.trans h h')
  have hqv' : ∀ {t : R}, D.lt t q → D.lt t v := by
    intro t ht
    rcases D.trichotomy q v with h | h | h
    · exact D.trans ht h.1
    · exact h.1 ▸ ht
    · exact absurd h.1 hqv
  obtain ⟨c, huc, hcq⟩ := D.dense huq
  have hcv : D.lt c v := hqv' hcq
  obtain ⟨m1, hm1c, hm1q, hm1⟩ := min_right C huc hcq hqv
  obtain ⟨m2, hum2, hm2c, hm2⟩ := min_left C huc hcv
  have hum1 : D.lt u m1 := by
    rcases D.trichotomy m1 c with h | h | h
    · exact absurd h.1 hm1c
    · rw [h.1]; exact huc
    · exact D.trans huc h.1
  have hm2q : D.lt m2 q := by
    rcases D.trichotomy c m2 with h | h | h
    · exact absurd h.1 hm2c
    · rw [← h.1]; exact hcq
    · exact D.trans h.1 hcq
  rcases C.Vtri (fv f u m1) (fv f u m2) with he | h12 | h21
  · have heq : m1 = m2 :=
      C.inj m1 m2 hum1 (hqv' hm1q) hum2 (hqv' hm2q) he
    refine ⟨m1, hum1, hm1q, ?_⟩
    intro y hyu hyq hyne
    by_cases hcy : D.lt c y
    · exact hm1 y (hasym hcy) hyq hyne
    · have : Vlt (fv f u m2) (fv f u y) :=
        hm2 y hyu hcy (fun hy => hyne (by rw [hy, heq]))
      rw [heq]; exact this
  · refine ⟨m1, hum1, hm1q, ?_⟩
    intro y hyu hyq hyne
    by_cases hcy : D.lt c y
    · exact hm1 y (hasym hcy) hyq hyne
    · by_cases hy2 : y = m2
      · rw [hy2]; exact h12
      · exact C.Vtr h12 (hm2 y hyu hcy hy2)
  · refine ⟨m2, hum2, hm2q, ?_⟩
    intro y hyu hyq hyne
    by_cases hcy : D.lt c y
    · by_cases hy1 : y = m1
      · rw [hy1]; exact h21
      · exact C.Vtr h21 (hm1 y (hasym hcy) hyq hy1)
    · exact hm2 y hyu hcy hyne

/-- Pairs `(x,q)` with `u < x < q ≤ v` for which `x` is the strict minimum of `f` on `(u,q)`. -/
def MinPair (Vlt : R → R → Prop) (f : DefinableFunction M I B) (u v : R) : Set (Power R 2) :=
  fun s => (D.lt u (s 0) ∧ D.lt (s 0) (s 1) ∧ ¬ D.lt v (s 1)) ∧
    NoBad2 Vlt f u (fun a b y => D.lt u y ∧ D.lt y b ∧ ¬ (y = a)) s

lemma minPair_definable (C : LocalExtCtx D M Vlt f u v) : M.S 2 (MinPair Vlt f u v) := by
  have hQ : M.S 3 (fun t : Power R 3 => D.lt u (t 2) ∧ D.lt (t 2) (t 1) ∧ ¬ (t 2 = t 0)) :=
    M.inter_mem (defin_const_lt M 2 u)
      (M.inter_mem (defin_lt M 2 1) (M.compl_mem (defin_eq M 2 0)))
  exact M.inter_mem
    (M.inter_mem (defin_const_lt M 0 u)
      (M.inter_mem (defin_lt M 0 1) (M.compl_mem (defin_const_lt M 1 v))))
    (noBad2_definable Vlt C.Vdef f u hQ)

/-- The set of points which are the strict minimum of `f` on some initial subinterval `(u,q)`. -/
def MinLocus (Vlt : R → R → Prop) (f : DefinableFunction M I B) (u v : R) : Set (Power R 1) :=
  fun x => ∃ q : Power R 1, MinPair Vlt f u v (Power.append x q)

lemma minLocus_definable (C : LocalExtCtx D M Vlt f u v) :
    M.S 1 (MinLocus Vlt f u v) :=
  M.existsLast_mem (n := 1) (m := 1) (minPair_definable C)

/-- Being the strict minimum on `(u,q)` puts a point in the minimum locus. -/
lemma minLocus_of {x q : R}
    (hux : D.lt u x) (hxq : D.lt x q) (hqv : ¬ D.lt v q)
    (hmin : ∀ y : R, D.lt u y → D.lt y q → ¬ (y = x) → Vlt (fv f u x) (fv f u y)) :
    MinLocus Vlt f u v (pt x) := by
  refine ⟨fun _ => q, ⟨hux, hxq, hqv⟩, ?_⟩
  rintro ⟨y, ⟨h1, h2, h3⟩, -, -, hnv⟩
  exact hnv (hmin y h1 h2 h3)

/-- An element of the minimum locus is the strict minimum on some `(u,q)` with `q ≤ v`. -/
lemma minLocus_elim (C : LocalExtCtx D M Vlt f u v) {x : R}
    (h : MinLocus Vlt f u v (pt x)) :
    D.lt u x ∧ ∃ q : R, D.lt x q ∧ ¬ D.lt v q ∧
      ∀ y : R, D.lt u y → D.lt y q → ¬ (y = x) → Vlt (fv f u x) (fv f u y) := by
  obtain ⟨Q, ⟨hux, hxq, hqv⟩, hnb⟩ := h
  have hle : ∀ {t : R}, D.lt t (Q 0) → D.lt t v := by
    intro t ht
    rcases D.trichotomy (Q 0) v with hh | hh | hh
    · exact D.trans ht hh.1
    · exact hh.1 ▸ ht
    · exact absurd hh.1 hqv
  refine ⟨hux, Q 0, hxq, hqv, ?_⟩
  intro y h1 h2 h3
  by_contra hnv
  exact hnb ⟨y, ⟨h1, h2, h3⟩, C.mem h1 (hle h2), C.mem hux (hle hxq), hnv⟩

/-- No interval of strict local extrema: the main theorem, in abstract form. -/
theorem no_local_extremum_interval (C : LocalExtCtx D M Vlt f u v) : False := by
  have hasym : ∀ {a b : R}, D.lt a b → ¬ D.lt b a := fun h h' => D.irrefl _ (D.trans h h')
  have hle : ∀ {t q' : R}, D.lt t q' → ¬ D.lt v q' → D.lt t v := by
    intro t q' ht hq'
    rcases D.trichotomy q' v with hh | hh | hh
    · exact D.trans ht hh.1
    · exact hh.1 ▸ ht
    · exact absurd hh.1 hq'
  have hno : ∀ p q : R, D.lt p q →
      ¬ (openInterval D (Endpoint.finite p) (Endpoint.finite q)).Subset
        (MinLocus Vlt f u v) := by
    intro p q hpq hsub
    obtain ⟨x, hpx, hxq⟩ := D.dense hpq
    have hxM := hsub (show openInterval D (Endpoint.finite p) (Endpoint.finite q) (pt x)
      from ⟨hpx, hxq⟩)
    obtain ⟨hux, q1, hxq1, hq1v, -⟩ := minLocus_elim C hxM
    have hxv : D.lt x v := hle hxq1 hq1v
    obtain ⟨d₁, d₂, -, hd1x, hxd2, -, hwin⟩ := C.loc x hux hxv
    obtain ⟨t, hxt, htq, htd2⟩ := exists_between_lt3 D hxq hxd2
    have htM := hsub (show openInterval D (Endpoint.finite p) (Endpoint.finite q) (pt t)
      from ⟨D.trans hpx hxt, htq⟩)
    obtain ⟨hut, qt, htqt, -, hmint⟩ := minLocus_elim C htM
    have hxne : ¬ (x = t) := fun he => D.irrefl x (by rw [he] at hxt ⊢; exact hxt)
    have h1 : Vlt (fv f u t) (fv f u x) := hmint x hux (D.trans hxt htqt) hxne
    have h2 : Vlt (fv f u x) (fv f u t) :=
      hwin t (D.trans hd1x hxt) htd2 (fun he => hxne he.symm)
    exact C.Virr _ (C.Vtr h2 h1)
  have hfin : IsFinite1 (MinLocus Vlt f u v) :=
    isFinite1_of_no_interval D ((M.ominimal _).1 (minLocus_definable C)) hno
  obtain ⟨m, hum, hmv, hmin⟩ := min_interval C C.uv (D.irrefl v)
  have hmM : MinLocus Vlt f u v (pt m) := minLocus_of hum hmv (D.irrefl v) hmin
  obtain ⟨x0, hx0M, hx0least⟩ := exists_least_of_finite D hfin hmM
  obtain ⟨hux0, q0, hx0q0, hq0v, -⟩ := minLocus_elim C hx0M
  have hx0v : D.lt x0 v := hle hx0q0 hq0v
  obtain ⟨m', hum', hm'x0, hmin'⟩ := min_interval C hux0 (hasym hx0v)
  exact hx0least m' (minLocus_of hum' hm'x0 (hasym hx0v) hmin') hm'x0

end NoExtremum

end Monotonicity_Theorem


/-! ### NoUniformExtremal -/


namespace Monotonicity_Theorem

section NoUniformExtremal

variable {R : Type} {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
  {I B : Set (Power R 1)}

/-- Injectivity of `f` on `(u,v)`, transported to the point-valued function `fv`. -/
lemma inj_fv_of_inj (f : DefinableFunction M I B) {u v : R}
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :
    ∀ x y : R, D.lt u x → D.lt x v → D.lt u y → D.lt y v → fv f u x = fv f u y → x = y := by
  intro x y hux hxv huy hyv hfe
  have hxI : I (pt x) := hsub ⟨hux, hxv⟩
  have hyI : I (pt y) := hsub ⟨huy, hyv⟩
  rw [fv_eq f u hxI, fv_eq f u hyI] at hfe
  have hval : (f.toFun (Subtype.mk (pt x) hxI)).1 = (f.toFun (Subtype.mk (pt y) hyI)).1 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    exact hfe
  exact congrFun (hinj (pt x) hxI ⟨hux, hxv⟩ (pt y) hyI ⟨huy, hyv⟩ (Subtype.ext hval)) 0

/-- The above-above pattern says that every point of `(u,v)` is a strict local minimum,
in the point-valued formulation used by `LocalExtCtx`. -/
lemma loc_of_uniformAboveAbove (f : DefinableFunction M I B) {u v : R}
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hU : UniformAboveAbove D f u v) :
    ∀ x : R, D.lt u x → D.lt x v →
      ∃ c₁ c₂ : R, D.lt u c₁ ∧ D.lt c₁ x ∧ D.lt x c₂ ∧ D.lt c₂ v ∧
        ∀ y : R, D.lt c₁ y → D.lt y c₂ → ¬ (y = x) → D.lt (fv f u x) (fv f u y) := by
  intro x hux hxv
  have hxI : I (pt x) := hsub ⟨hux, hxv⟩
  obtain ⟨c₁, c₂, hc1J, hc2J, hc1x, hxc2, hleft, hright⟩ := hU (pt x) hxI ⟨hux, hxv⟩
  refine ⟨c₁ 0, c₂ 0, hc1J.1, hc1x, hxc2, hc2J.2, ?_⟩
  intro y hy1 hy2 hyne
  have huy : D.lt u y := D.trans hc1J.1 hy1
  have hyv : D.lt y v := D.trans hy2 hc2J.2
  have hyI : I (pt y) := hsub ⟨huy, hyv⟩
  rw [fv_eq f u hxI, fv_eq f u hyI]
  rcases D.trichotomy y x with h | h | h
  · exact hleft (pt y) hyI ⟨huy, hyv⟩ hy1 h.1
  · exact absurd h.1 hyne
  · exact hright (pt y) hyI ⟨huy, hyv⟩ h.1 hy2

/-- The below-below pattern says that every point of `(u,v)` is a strict local maximum,
in the point-valued formulation used by `LocalExtCtx` (with the reversed value order). -/
lemma loc_of_uniformBelowBelow (f : DefinableFunction M I B) {u v : R}
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hU : UniformBelowBelow D f u v) :
    ∀ x : R, D.lt u x → D.lt x v →
      ∃ c₁ c₂ : R, D.lt u c₁ ∧ D.lt c₁ x ∧ D.lt x c₂ ∧ D.lt c₂ v ∧
        ∀ y : R, D.lt c₁ y → D.lt y c₂ → ¬ (y = x) → D.lt (fv f u y) (fv f u x) := by
  intro x hux hxv
  have hxI : I (pt x) := hsub ⟨hux, hxv⟩
  obtain ⟨c₁, c₂, hc1J, hc2J, hc1x, hxc2, hleft, hright⟩ := hU (pt x) hxI ⟨hux, hxv⟩
  refine ⟨c₁ 0, c₂ 0, hc1J.1, hc1x, hxc2, hc2J.2, ?_⟩
  intro y hy1 hy2 hyne
  have huy : D.lt u y := D.trans hc1J.1 hy1
  have hyv : D.lt y v := D.trans hy2 hc2J.2
  have hyI : I (pt y) := hsub ⟨huy, hyv⟩
  rw [fv_eq f u hxI, fv_eq f u hyI]
  rcases D.trichotomy y x with h | h | h
  · exact hleft (pt y) hyI ⟨huy, hyv⟩ hy1 h.1
  · exact absurd h.1 hyne
  · exact hright (pt y) hyI ⟨huy, hyv⟩ h.1 hy2

/-- An injective definable function cannot have every point of an interval as a strict
local minimum. -/
theorem not_uniform_above_above_core (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    (hU : UniformAboveAbove D f u v) :
    False := by
  refine no_local_extremum_interval (Vlt := fun a b => D.lt a b) (f := f) (u := u) (v := v)
    { Virr := fun a => D.irrefl a
      Vtr := fun h₁ h₂ => D.trans h₁ h₂
      Vtri := ?_
      Vdef := fun i j => defin_lt M i j
      uv := huv
      sub := hsub
      loc := loc_of_uniformAboveAbove f hsub hU
      inj := inj_fv_of_inj f hsub hinj }
  intro a b
  rcases D.trichotomy a b with h | h | h
  · exact Or.inr (Or.inl h.1)
  · exact Or.inl h.1
  · exact Or.inr (Or.inr h.1)

/-- An injective definable function cannot have every point of an interval as a strict
local maximum. -/
theorem not_uniform_below_below_core (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    (hU : UniformBelowBelow D f u v) :
    False := by
  refine no_local_extremum_interval (Vlt := fun a b => D.lt b a) (f := f) (u := u) (v := v)
    { Virr := fun a => D.irrefl a
      Vtr := fun h₁ h₂ => D.trans h₂ h₁
      Vtri := ?_
      Vdef := fun i j => defin_lt M j i
      uv := huv
      sub := hsub
      loc := loc_of_uniformBelowBelow f hsub hU
      inj := ?_ }
  · intro a b
    rcases D.trichotomy a b with h | h | h
    · exact Or.inr (Or.inr h.1)
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
  · exact inj_fv_of_inj f hsub hinj

end NoUniformExtremal

end Monotonicity_Theorem


open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : forall x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      forall y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    (hU : UniformAboveAbove D f u v) :
    False :=
  Monotonicity_Theorem.not_uniform_above_above_core D M f u v huv hsub hinj hU
