-- Prove2me | solution 1 for Monotonicity_Theorem.pattern_at_interior_point
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:56:46.656106+00:00
-- url     : https://prove2.me/submissions/baa4ec7c-030a-4bb1-b2c1-b34fca0b4561

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_above_sign_definable
import Theorems.Thm_Monotonicity_Theorem_below_sign_definable
import Theorems.Thm_Monotonicity_Theorem_left_adjacent_cut
import Theorems.Thm_Monotonicity_Theorem_right_adjacent_cut

open Monotonicity_Theorem

namespace Monotonicity_Theorem

theorem covLeftAux {R : Type} (x y : Power R 1) :
    Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem covRightAux {R : Type} (x y : Power R 1) :
    Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y := by
  funext j
  exact Fin.append_right x y j

-- Read off v as the output tuple from a graph witness.
theorem covOutEq {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {a b : Endpoint R} {B : Set (Power R 1)}
    (M : OMinimalStructure D)
    (f : DefinableFunction M (openInterval D a b) B)
    {y v : Power R 1} (hy : openInterval D a b y)
    (hG : FunctionGraph (R := R) (m := 1) (n := 1)
      (A := openInterval D a b) (B := B) f.toFun (Power.append y v)) :
    v = (f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1 := by
  obtain ⟨hx', hEq⟩ := hG
  have eL : Power.left (Power.append y v) = y := covLeftAux y v
  have eR : Power.right (Power.append y v) = v := covRightAux y v
  have hSub : (⟨Power.left (Power.append y v), hx'⟩
      : {x : Power R 1 // openInterval D a b x})
      = (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x}) := Subtype.ext eL
  rw [eR, hSub] at hEq
  exact hEq

end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {a b : Endpoint R} {B : Set (Power R 1)}
    (f : DefinableFunction M (openInterval D a b) B)
    (hinj : forall x y (hx : openInterval D a b x) (hy : openInterval D a b y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    {p : Power R 1} (hp : openInterval D a b p) :
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1)) \/
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1)) \/
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1)) \/
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1)) := by
  -- Step 0: witness coords on both sides.
  have hr1 : ∃ r1 : R, Endpoint.lt D a (Endpoint.finite r1) ∧ D.lt r1 (p 0) := by
    cases a with
    | negInf =>
      obtain ⟨r1, hr1⟩ := D.no_left_endpoint (p 0)
      exact ⟨r1, trivial, hr1⟩
    | finite av =>
      have hav : D.lt av (p 0) := hp.left
      obtain ⟨r1, hr1a, hr1p⟩ := D.dense hav
      exact ⟨r1, hr1a, hr1p⟩
    | posInf =>
      exact False.elim hp.left
  have hr2 : ∃ r2 : R, D.lt (p 0) r2 ∧ Endpoint.lt D (Endpoint.finite r2) b := by
    cases b with
    | negInf =>
      exact False.elim hp.right
    | finite bv =>
      have hpb : D.lt (p 0) bv := hp.right
      obtain ⟨r2, hr2p, hr2b⟩ := D.dense hpb
      exact ⟨r2, hr2p, hr2b⟩
    | posInf =>
      obtain ⟨r2, hr2⟩ := D.no_right_endpoint (p 0)
      exact ⟨r2, hr2, trivial⟩
  obtain ⟨r1, hr1a, hr1p⟩ := hr1
  obtain ⟨r2, hr2p, hr2b⟩ := hr2
  -- Windows and threshold.
  have hJl : M.S 1 (openInterval D (Endpoint.finite r1) (Endpoint.finite (p 0))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hJr : M.S 1 (openInterval D (Endpoint.finite (p 0)) (Endpoint.finite r2)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  set t : R := ((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0 with htdef
  have hSpL := Monotonicity_Theorem.above_sign_definable D M f
    (openInterval D (Endpoint.finite r1) (Endpoint.finite (p 0))) hJl t
  have hSmL := Monotonicity_Theorem.below_sign_definable D M f _ hJl t
  have hSpR := Monotonicity_Theorem.above_sign_definable D M f _ hJr t
  have hSmR := Monotonicity_Theorem.below_sign_definable D M f _ hJr t
  -- Windows lie in the domain.
  have hwinL : ∀ y : Power R 1,
      openInterval D (Endpoint.finite r1) (Endpoint.finite (p 0)) y →
      openInterval D a b y := by
    intro y hy
    have hy1 : D.lt r1 (Power.coord1 y) := hy.left
    have hy2 : D.lt (Power.coord1 y) (p 0) := hy.right
    have ha : Endpoint.lt D a (Endpoint.finite (y 0)) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : D.lt av r1 := hr1a
        exact D.trans g0 hy1
      | posInf => exact False.elim hr1a
    have hb : Endpoint.lt D (Endpoint.finite (y 0)) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g1 : D.lt (p 0) bv := hp.right
        exact D.trans hy2 g1
      | posInf => exact trivial
    exact ⟨ha, hb⟩
  have hwinR : ∀ y : Power R 1,
      openInterval D (Endpoint.finite (p 0)) (Endpoint.finite r2) y →
      openInterval D a b y := by
    intro y hy
    have hy1 : D.lt (Power.coord1 y) r2 := hy.right
    have hy2 : D.lt (p 0) (Power.coord1 y) := hy.left
    have ha : Endpoint.lt D a (Endpoint.finite (y 0)) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : D.lt av (p 0) := hp.left
        exact D.trans g0 hy2
      | posInf => exact False.elim hp.left
    have hb : Endpoint.lt D (Endpoint.finite (y 0)) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g1 : D.lt r2 bv := hr2b
        exact D.trans hy1 g1
      | posInf => exact trivial
    exact ⟨ha, hb⟩
  -- Covers by sign on each side.
  have hcovL : ∀ y : Power R 1,
      openInterval D (Endpoint.finite r1) (Endpoint.finite (p 0)) y →
      ((fun y => openInterval D (Endpoint.finite r1) (Endpoint.finite (p 0)) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval D a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 D (fun _ => t) v) y ∨
       (fun y => openInterval D (Endpoint.finite r1) (Endpoint.finite (p 0)) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval D a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 D v (fun _ => t)) y) := by
    intro y hy
    have hyJ : openInterval D a b y := hwinL y hy
    have hylt : D.lt (Power.coord1 y) (p 0) := hy.right
    rcases D.trichotomy (Power.coord1 ((f.toFun (⟨y, hyJ⟩
      : {x : Power R 1 // openInterval D a b x})).1)) t with
      ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hlt, _, _⟩
    · refine Or.inr ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval D a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval D a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval D a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval D a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1 D
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1)
            (fun _ => t) := hlt
        exact hO
    · have hteq : (f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval D a b x})).1
          = (f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1 := by
        funext i
        have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
        rw [i0]
        show (((f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval D a b x})).1)) 0 = t
        exact heq
      have hSub : y = p :=
        hinj _ _ _ _ (Subtype.ext hteq)
      have hylt2 : D.lt (Power.coord1 y) (p 0) := hy.right
      rw [hSub] at hylt2
      exact False.elim (D.irrefl _ hylt2)
    · refine Or.inl ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval D a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval D a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval D a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval D a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1 D (fun _ => t)
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1) := hlt
        exact hO
  -- Cover on the right by sign.
  have hcovR : ∀ y : Power R 1,
      openInterval D (Endpoint.finite (p 0)) (Endpoint.finite r2) y →
      ((fun y => openInterval D (Endpoint.finite (p 0)) (Endpoint.finite r2) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval D a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 D (fun _ => t) v) y ∨
       (fun y => openInterval D (Endpoint.finite (p 0)) (Endpoint.finite r2) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval D a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 D v (fun _ => t)) y) := by
    intro y hy
    have hyJ : openInterval D a b y := hwinR y hy
    rcases D.trichotomy (Power.coord1 ((f.toFun (⟨y, hyJ⟩
      : {x : Power R 1 // openInterval D a b x})).1)) t with
      ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hlt, _, _⟩
    · refine Or.inr ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval D a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval D a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval D a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval D a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1 D
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1)
            (fun _ => t) := hlt
        exact hO
    · have hteq : (f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval D a b x})).1
          = (f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1 := by
        funext i
        have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
        rw [i0]
        show (((f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval D a b x})).1)) 0 = t
        exact heq
      have hSub : y = p :=
        hinj _ _ _ _ (Subtype.ext hteq)
      have hylt2 : D.lt (p 0) (Power.coord1 y) := hy.left
      rw [hSub] at hylt2
      exact False.elim (D.irrefl _ hylt2)
    · refine Or.inl ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval D a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval D a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval D a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval D a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval D a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1 D (fun _ => t)
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval D a b x})).1) := hlt
        exact hO
  -- Adjacency cuts on both sides.
  obtain ⟨Mc, hMp, hMbound, hPureL⟩ :=
    Monotonicity_Theorem.left_adjacent_cut D M hSpL hSmL hr1p hcovL
  obtain ⟨Nc, hNp, hNbound, hPureR⟩ :=
    Monotonicity_Theorem.right_adjacent_cut D M hSpR hSmR hr2p hcovR
  -- Cut points lie in the domain.
  have hMcJ : openInterval D a b (fun _ => Mc) := by
    have hlow : Endpoint.lt D a (Endpoint.finite Mc) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : D.lt av r1 := hr1a
        cases hMbound with
        | inl h => exact D.trans g0 h
        | inr heq =>
          rw [← heq]
          exact g0
      | posInf => exact False.elim hr1a
    have hhigh : Endpoint.lt D (Endpoint.finite Mc) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g1 : D.lt (p 0) bv := hp.right
        exact D.trans hMp g1
      | posInf => exact trivial
    exact ⟨hlow, hhigh⟩
  have hNcJ : openInterval D a b (fun _ => Nc) := by
    have hlow : Endpoint.lt D a (Endpoint.finite Nc) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : D.lt av (p 0) := hp.left
        exact D.trans g0 hNp
      | posInf => exact False.elim hp.left
    have hhigh : Endpoint.lt D (Endpoint.finite Nc) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g2 : D.lt r2 bv := hr2b
        cases hNbound with
        | inl h => exact D.trans h g2
        | inr heq =>
          rw [heq]
          exact g2
      | posInf => exact trivial
    exact ⟨hlow, hhigh⟩
  have hMcLt : Lt1 D (fun _ => Mc) p := hMp
  have hNcLt : Lt1 D p (fun _ => Nc) := hNp
  rcases hPureL with hPL | hPL
  · rcases hPureR with hPR | hPR
    · -- ++ : above on both sides
      refine Or.inl ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt D (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : D.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt t (v 0) := hOv
        show D.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt D (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : D.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt t (v 0) := hOv
        show D.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
    · -- +- : above left, below right
      refine Or.inr (Or.inl ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩)
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt D (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : D.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt t (v 0) := hOv
        show D.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt D (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : D.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt (v 0) t := hOv
        show D.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
  · rcases hPureR with hPR | hPR
    · -- -+ : below left, above right
      refine Or.inr (Or.inr (Or.inl ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩))
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt D (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : D.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt (v 0) t := hOv
        show D.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt D (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : D.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt t (v 0) := hOv
        show D.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
    · -- -- : below on both sides
      refine Or.inr (Or.inr (Or.inr ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩))
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt D (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : D.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt (v 0) t := hOv
        show D.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval D (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt D (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt D (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : D.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : D.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq D M f hy hG
        have g1 : D.lt (v 0) t := hOv
        show D.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval D a b x})).1) 0)
        rw [← hev]
        exact g1
