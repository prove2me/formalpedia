-- Prove2me | solution 1 for Monotonicity_Theorem.constant_or_injective_subinterval
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T06:19:02.114404+00:00
-- url     : https://prove2.me/submissions/3f1ce76a-1341-4be3-be33-4116ccf579a5

import Theorems.Thm_Monotonicity_Theorem_definable_preimage
import Definitions.Def_Monotonicity_Theorem_Window_Loci

set_option autoImplicit false

namespace Monotonicity_Theorem

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



variable {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
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
theorem const_or_inj_main (D : DenseLinearOrderNoEndpoints R)
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



end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I) :
    exists u1 v1 : R, D.lt u1 v1 ∧
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) ∧
      (ConstOnInterval f u1 v1 ∨
        ∀ x (hx : I x), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
          ∀ y (hy : I y), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) y →
            f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :=
  Monotonicity_Theorem.const_or_inj_main D M f u v huv hsub
