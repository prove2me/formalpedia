-- Prove2me | solution 1 for Monotonicity_Theorem.window_loci_definable
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T21:03:41.221245+00:00
-- url     : https://prove2.me/submissions/85ab25f4-7aeb-4afd-a9fd-445956ee041a

import Definitions.Def_Monotonicity_Theorem_Window_Loci

set_option autoImplicit false

open Monotonicity_Theorem

namespace WindowLociAux

lemma power1_ext {R : Type} {a b : Power R 1} (h : a 0 = b 0) : a = b := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  exact h


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


end Properties

end WindowLociAux

open WindowLociAux in
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B) :
    M.S 1 (ConstWindowLocus f) ∧ M.S 1 (IncWindowLocus f) ∧ M.S 1 (DecWindowLocus f) := by
  refine ⟨locus_definable M _ (const_prop_definable f), ?_, ?_⟩
  · exact locus_definable M _
      (M.inter_mem (subset_prop_definable f.domain_mem) (inc_prop_definable f))
  · exact locus_definable M _
      (M.inter_mem (subset_prop_definable f.domain_mem) (dec_prop_definable f))
