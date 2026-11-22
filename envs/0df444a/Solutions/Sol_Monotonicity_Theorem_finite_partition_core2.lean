-- Prove2me | solution 1 for Monotonicity_Theorem.finite_partition_core2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T00:48:59.921643+00:00
-- url     : https://prove2.me/submissions/807ec262-0bfe-4d0c-98a6-749e78a1678c

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_const_cont_of_const
import Theorems.Thm_Monotonicity_Theorem_lemma_three2
import Mathlib.Tactic.FinCases
import Theorems.Thm_Monotonicity_Theorem_lemma_one
import Theorems.Thm_Monotonicity_Theorem_lemma_two
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval2

open Classical
open Monotonicity_Theorem

namespace Monotonicity_Theorem

-- Index maps for the discontinuity matrix, inlined from DiscTower (that module
-- cannot be imported alongside Framework2 on the server: it transitively pulls
-- the old Framework, whose `Power` clashes with Framework2's).
-- Points are determined by coordinates.
theorem ptLam {R : Type} (x : Power R 1) : x = fun _ => Power.coord1 x := by
  funext k
  have hk : k.val = 0 := by
    have := k.isLt
    omega
  have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
  rw [ek]
  rfl

-- Slots: 0:x, 1:w0, 2:e1, 3:e2, 4:d1, 5:d2, 6:y, 7:q.
def dIx : Fin 1 → Fin 8 := fun _ => ⟨0, by decide⟩
def dGy : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨6, by decide⟩ else ⟨7, by decide⟩
def dD1y : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨6, by decide⟩
def dYD2 : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨6, by decide⟩ else ⟨5, by decide⟩
def dE1q : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨7, by decide⟩
def dQe2 : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨7, by decide⟩ else ⟨3, by decide⟩
-- Delta maps at arity 6 (tuple x,w0,e1,e2,d1,d2).
def dD1x6 : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨0, by decide⟩
def dXD26 : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨5, by decide⟩
-- Graph/epsilon maps at arity 4 (tuple x,w0,e1,e2).
def dGx4 : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
def dE1w4 : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨1, by decide⟩
def dWe24 : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨3, by decide⟩

end Monotonicity_Theorem

namespace Monotonicity_Theorem

-- Inlined order-bound infrastructure (so this public proof needs no private imports).
def IsUpperBound1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (b : R) : Prop :=
  ∀ x : Power R 1, A x → (LT.lt (Power.coord1 x) b ∨ Power.coord1 x = b)

def BoundedAbove1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) : Prop :=
  ∃ b : R, IsUpperBound1 A b

def IsSupremum1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (s : R) : Prop :=
  IsUpperBound1 A s ∧
  ∀ b : R, IsUpperBound1 A b → (LT.lt s b ∨ s = b)

noncomputable def max1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : R) : R :=
  if LT.lt a b then b else a

end Monotonicity_Theorem

theorem Monotonicity_Theorem.disc_witness_aux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (p : Power R 1) (hpI : I p)
    (hNC : ¬ ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun) p) :
    ∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
        (Power.append p t) := by
  have hNR : ¬ ∀ w₀ : R,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 p) (fun _ => w₀)) →
      ∀ ε₁ ε₂ : R, ε₁ < w₀ → w₀ < ε₂ →
        ∃ δ₁ δ₂ : R, δ₁ < Power.coord1 p ∧ Power.coord1 p < δ₂ ∧
          ∀ y v : R, I (fun _ => y) →
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (n := 1) (m := 1) (fun _ => y) (fun _ => v)) →
            δ₁ < y → y < δ₂ → ε₁ < v ∧ v < ε₂ := by
    intro hR
    apply hNC
    refine ⟨hpI, hR⟩
  rw [not_forall] at hNR
  obtain ⟨w₀, hw₀⟩ := hNR
  rw [not_imp_iff_and_not] at hw₀
  obtain ⟨hGw, hw₁⟩ := hw₀
  rw [not_forall] at hw₁
  obtain ⟨e₁, hw₂⟩ := hw₁
  rw [not_forall] at hw₂
  obtain ⟨e₂, hw₃⟩ := hw₂
  rw [not_imp_iff_and_not] at hw₃
  obtain ⟨he₁w, hw₄⟩ := hw₃
  rw [not_imp_iff_and_not] at hw₄
  obtain ⟨hwe₂, hw₅⟩ := hw₄
  rw [not_exists] at hw₅
  refine ⟨fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂, ?_, ?_, ?_, ?_⟩
  · -- Graph part.
    have eG : (fun j : Fin (1 + 1) => (Power.append p
        (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) (dGx4 j)) =
        Power.append (fun _ => Power.coord1 p) (fun _ => w₀) := by
      funext j
      fin_cases j <;> rfl
    rw [eG]
    exact hGw
  · -- Epsilon below.
    have e1 : ((fun j : Fin 2 => (Power.append p
        (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) (dE1w4 j)) 0) = e₁ := by
      rfl
    have e2 : ((fun j : Fin 2 => (Power.append p
        (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) (dE1w4 j)) 1) = w₀ := by
      rfl
    rw [e1, e2]
    exact he₁w
  · -- Epsilon above.
    have e1 : ((fun j : Fin 2 => (Power.append p
        (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) (dWe24 j)) 0) = w₀ := by
      rfl
    have e2 : ((fun j : Fin 2 => (Power.append p
        (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) (dWe24 j)) 1) = e₂ := by
      rfl
    rw [e1, e2]
    exact hwe₂
  · -- Every delta window carries a bad point.
    intro hEx
    obtain ⟨d, hd⟩ := hEx
    obtain ⟨hd1, hd2, hG6⟩ := hd
    have hd1' : LT.lt (d 0) (Power.coord1 p) := hd1
    have hd2' : LT.lt (Power.coord1 p) (d 1) := hd2
    have hNB : ¬ ∀ y v : R, I (fun _ => y) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (n := 1) (m := 1) (fun _ => y) (fun _ => v)) →
        (d 0) < y → y < (d 1) → e₁ < v ∧ v < e₂ := by
      intro hAll
      exact hw₅ (d 0) ⟨d 1, hd1', hd2', hAll⟩
    rw [not_forall] at hNB
    obtain ⟨y, hy⟩ := hNB
    rw [not_forall] at hy
    obtain ⟨v, hv⟩ := hy
    rw [not_imp_iff_and_not] at hv
    obtain ⟨hyI, hv₁⟩ := hv
    rw [not_imp_iff_and_not] at hv₁
    obtain ⟨hGyv, hv₂⟩ := hv₁
    rw [not_imp_iff_and_not] at hv₂
    obtain ⟨hdy, hnev⟩ := hv₂
    rw [not_imp_iff_and_not] at hnev
    obtain ⟨hdy1, hnev'⟩ := hnev
    apply hG6
    refine ⟨fun k : Fin 2 => if _ : k.val = 0 then y else v, ?_, ?_, ?_, ?_, ?_⟩
    · -- I-point (base point p).
      have eI : (fun i : Fin 1 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          ((fun k : Fin 2 => if _ : k.val = 0 then y else v)) (dIx i)) = p := by
        funext i
        fin_cases i
        rfl
      rw [eI]
      exact hpI
    · -- Graph value.
      have eG : (fun j : Fin (1 + 1) => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dGy j)) =
          Power.append (fun _ => y) (fun _ => v) := by
        funext j
        fin_cases j <;> rfl
      rw [eG]
      exact hGyv
    · -- Delta below.
      have eD : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dD1y j)) 0) = (d 0) := by
        rfl
      have eD' : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dD1y j)) 1) = y := by
        rfl
      rw [eD, eD']
      exact hdy
    · -- Delta above.
      have eD : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dYD2 j)) 0) = y := by
        rfl
      have eD' : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dYD2 j)) 1) = (d 1) := by
        rfl
      rw [eD, eD']
      exact hdy1
    · -- Outside epsilon.
      have eE1a : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dE1q j)) 0) = e₁ := by
        rfl
      have eE1b : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dE1q j)) 1) = v := by
        rfl
      have eE2a : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dQe2 j)) 0) = v := by
        rfl
      have eE2b : ((fun j : Fin 2 => Power.append (Power.append (Power.append p
          (fun j : Fin 3 => if _ : j.val = 0 then w₀ else if _ : j.val = 1 then e₁ else e₂)) d)
          (fun k : Fin 2 => if _ : k.val = 0 then y else v) (dQe2 j)) 1) = e₂ := by
        rfl
      rw [eE1a, eE1b, eE2a, eE2b]
      exact hnev'

namespace Monotonicity_Theorem

theorem appendLeftAux {R : Type} {n m : Nat} (x : Power R n) (y : Power R m) :
    Power.left (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem appendRightAux {R : Type} {n m : Nat} (x : Power R n) (y : Power R m) :
    Power.right (Power.append x y) = y := by
  funext j
  exact Fin.append_right x y j

theorem loTrans {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (a : Endpoint R)
    {c d : R} (h : Endpoint.lt a (Endpoint.finite c)) (hlt : LT.lt c d) :
    Endpoint.lt a (Endpoint.finite d) := by
  cases a with
  | negInf => exact trivial
  | finite val => exact lt_trans h hlt
  | posInf => exact False.elim h

theorem hiTrans {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (b : Endpoint R)
    {c d : R} (h : Endpoint.lt (Endpoint.finite d) b) (hlt : LT.lt c d) :
    Endpoint.lt (Endpoint.finite c) b := by
  cases b with
  | negInf => exact False.elim h
  | finite val => exact lt_trans hlt h
  | posInf => exact trivial

theorem allBelow {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {p q r : R} (hpq : LT.lt p q) (hpr : LT.lt p r) :
    ∃ s : R, LT.lt p s ∧ LT.lt s q ∧ LT.lt s r := by
  obtain ⟨s1, hps1, hs1q⟩ := exists_between hpq
  rcases lt_trichotomy s1 r with hlt1 | heq1 | hlt2
  · exact ⟨s1, hps1, hs1q, hlt1⟩
  · have heq := heq1
    obtain ⟨s2, hps2, hs2⟩ := exists_between hps1
    refine ⟨s2, hps2, lt_trans hs2 hs1q, ?_⟩
    rw [← heq]
    exact hs2
  · have hlt := hlt2
    obtain ⟨s2, hps2, hs2r⟩ := exists_between hpr
    exact ⟨s2, hps2, lt_trans hs2r (lt_trans hlt hs1q), hs2r⟩

theorem ptEqAux {R : Type} {p q : Power R 1}
    (h : Power.coord1 p = Power.coord1 q) : p = q := by
  funext i
  have hiv : i.val < 1 := i.isLt
  have hi0 : i.val = 0 := by omega
  have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
  rw [hi]
  exact h

end Monotonicity_Theorem

open Monotonicity_Theorem

-- Inlined supremum tower (so this public proof needs no private imports).
theorem supUnionAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A B : Set (Power R 1)) (sA sB : R)
    (hSupA : IsSupremum1 A sA)
    (hSupB : IsSupremum1 B sB) :
    IsSupremum1 ((A ∪ B)) (max1 sA sB) := by
  rcases hSupA with ⟨h_sA_upper, h_sA_least⟩
  rcases hSupB with ⟨h_sB_upper, h_sB_least⟩
  constructor
  · intro x hx
    show LT.lt (Power.coord1 x) (if LT.lt sA sB then sB else sA) ∨
      Power.coord1 x = (if LT.lt sA sB then sB else sA)
    by_cases h : LT.lt sA sB
    · rw [if_pos h]
      cases hx with
      | inl hxA =>
        have h1 := h_sA_upper x hxA
        cases h1 with
        | inl hlt => left; exact lt_trans hlt h
        | inr heq => left; rw [heq]; exact h
      | inr hxB =>
        exact h_sB_upper x hxB
    · rw [if_neg h]
      cases hx with
      | inl hxA =>
        exact h_sA_upper x hxA
      | inr hxB =>
        have h2 := h_sB_upper x hxB
        rcases lt_trichotomy sA sB with hlt | heq | hgt
        · contradiction
        · cases h2 with
          | inl hlt2 => left; rw [heq]; exact hlt2
          | inr heq2 => right; rw [heq]; exact heq2
        · cases h2 with
          | inl hlt2 => left; exact lt_trans hlt2 hgt
          | inr heq2 => left; rw [heq2]; exact hgt
  · intro b hb
    have hbA : IsUpperBound1 A b := fun x hx => hb x (Or.inl hx)
    have hbB : IsUpperBound1 B b := fun x hx => hb x (Or.inr hx)
    have hA_le_b := h_sA_least b hbA
    have hB_le_b := h_sB_least b hbB
    show LT.lt (if LT.lt sA sB then sB else sA) b ∨
      (if LT.lt sA sB then sB else sA) = b
    by_cases h : LT.lt sA sB
    · rw [if_pos h]
      exact hB_le_b
    · rw [if_neg h]
      exact hA_le_b

theorem supOpenIntervalAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a : Endpoint R) (b : R)
    (hNotEmpty : (openInterval a (Endpoint.finite b)).Nonempty) :
    IsSupremum1 (openInterval a (Endpoint.finite b)) b := by
  constructor
  · intro x hx
    have hx' : LT.lt (Power.coord1 x) b := hx.right
    exact Or.inl hx'
  · intro y hy
    rcases lt_trichotomy b y with hby | heq | hyb
    · exact Or.inl hby
    · exact Or.inr heq
    · obtain ⟨x0, hx0left, hx0right⟩ := hNotEmpty
      have hm_lt_b : LT.lt (max1 y (Power.coord1 x0)) b := by
        show LT.lt (if LT.lt y (Power.coord1 x0) then Power.coord1 x0 else y) b
        by_cases h : LT.lt y (Power.coord1 x0)
        · rw [if_pos h]
          have hr : LT.lt (Power.coord1 x0) b := hx0right
          exact hr
        · rw [if_neg h]
          exact hyb
      obtain ⟨z, hm_lt_z, hz_lt_b⟩ := exists_between hm_lt_b
      have ha_lt_z : Endpoint.lt a (Endpoint.finite z) := by
        by_cases h : LT.lt y (Power.coord1 x0)
        · have hmax : max1 y (Power.coord1 x0) = Power.coord1 x0 := by
            show (if LT.lt y (Power.coord1 x0) then Power.coord1 x0 else y)
              = Power.coord1 x0
            rw [if_pos h]
          rw [hmax] at hm_lt_z
          have hmz : LT.lt (Power.coord1 x0) z := hm_lt_z
          cases a with
          | negInf => exact trivial
          | finite val =>
            have g : LT.lt val (Power.coord1 x0) := hx0left
            exact lt_trans g hmz
          | posInf => exact False.elim hx0left
        · have hx0_le_y : LT.lt (Power.coord1 x0) y ∨ Power.coord1 x0 = y := by
            rcases lt_trichotomy (Power.coord1 x0) y with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr h2
            · exact absurd h3 h
          have hmax : max1 y (Power.coord1 x0) = y := by
            show (if LT.lt y (Power.coord1 x0) then Power.coord1 x0 else y) = y
            rw [if_neg h]
          rw [hmax] at hm_lt_z
          have hx0_lt_z : LT.lt (Power.coord1 x0) z := by
            cases hx0_le_y with
            | inl hlt => exact lt_trans hlt hm_lt_z
            | inr heq2 =>
              have hm2 : LT.lt y z := hm_lt_z
              rw [heq2]
              exact hm2
          cases a with
          | negInf => exact trivial
          | finite val =>
            have g : LT.lt val (Power.coord1 x0) := hx0left
            exact lt_trans g hx0_lt_z
          | posInf => exact False.elim hx0left
      have hzmem : openInterval a (Endpoint.finite b) (fun _ => z) :=
        ⟨ha_lt_z, hz_lt_b⟩
      have hz_le_y := hy (fun _ => z) hzmem
      have hy_lt_z : LT.lt y z := by
        by_cases h : LT.lt y (Power.coord1 x0)
        · have hmax : max1 y (Power.coord1 x0) = Power.coord1 x0 := by
            show (if LT.lt y (Power.coord1 x0) then Power.coord1 x0 else y)
              = Power.coord1 x0
            rw [if_pos h]
          rw [hmax] at hm_lt_z
          exact lt_trans h hm_lt_z
        · have hmax : max1 y (Power.coord1 x0) = y := by
            show (if LT.lt y (Power.coord1 x0) then Power.coord1 x0 else y) = y
            rw [if_neg h]
          rw [hmax] at hm_lt_z
          exact hm_lt_z
      cases hz_le_y with
      | inl hlt =>
        have hlt' : LT.lt z y := hlt
        exact False.elim (lt_irrefl y (lt_trans hy_lt_z hlt'))
      | inr heq =>
        have heq' : z = y := heq
        rw [heq'] at hy_lt_z
        exact False.elim (lt_irrefl y hy_lt_z)

theorem supCompletenessAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1))
    (hDef : FiniteUnionOfPointsAndIntervals A)
    (hNotEmpty : A.Nonempty)
    (hBounded : BoundedAbove1 A) :
    ∃ s : R, IsSupremum1 A s := by
  have hCore : ∀ (A : Set (Power R 1)),
      FiniteUnionOfPointsAndIntervals A ->
      BoundedAbove1 A → (∀ x, ¬ A x) ∨ (∃ s : R, IsSupremum1 A s) := by
    intro A hDef
    induction hDef with
    | empty =>
      intro hBounded
      left
      intro x hx
      exact hx
    | point =>
      rename_i a
      intro hBounded
      right
      use a
      constructor
      · intro x hx
        right
        exact hx
      · intro b hb
        let x_a : Power R 1 := fun _ => a
        have hx_in_set : pointSet a x_a := by rfl
        have h1 := hb x_a hx_in_set
        cases h1 with
        | inl hlt => exact Or.inl hlt
        | inr heq => exact Or.inr heq
    | interval =>
      rename_i a b
      cases b with
      | negInf =>
        intro _
        left
        intro x hx
        exact hx.right
      | finite val =>
        intro _
        by_cases hEmpty : (openInterval a (Endpoint.finite val)).Nonempty
        · right
          use val
          exact supOpenIntervalAux a val hEmpty
        · left
          intro x hx
          exact hEmpty ⟨x, hx⟩
      | posInf =>
        cases a with
        | negInf =>
          intro hBounded
          by_cases hEmpty : (openInterval (R := R) Endpoint.negInf Endpoint.posInf).Nonempty
          · obtain ⟨x0, -, -⟩ := hEmpty
            rcases hBounded with ⟨M, hM_upper⟩
            obtain ⟨y, hym⟩ := exists_gt (max1 M (Power.coord1 x0))
            have hM_lt_y : LT.lt M y := by
              by_cases h : LT.lt M (Power.coord1 x0)
              · have hmax : max1 M (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if LT.lt M (Power.coord1 x0) then Power.coord1 x0 else M)
                    = Power.coord1 x0
                  rw [if_pos h]
                rw [hmax] at hym
                exact lt_trans h hym
              · have hmax : max1 M (Power.coord1 x0) = M := by
                  show (if LT.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                  rw [if_neg h]
                rw [hmax] at hym
                exact hym
            have hz_gt_a : Endpoint.lt Endpoint.negInf (Endpoint.finite y) := trivial
            let y_pow : Power R 1 := fun _ => y
            have hy_in : openInterval Endpoint.negInf Endpoint.posInf y_pow :=
              ⟨hz_gt_a, trivial⟩
            have hy_le_M := hM_upper y_pow hy_in
            cases hy_le_M with
            | inl hlt =>
              exact False.elim (lt_irrefl M (lt_trans hM_lt_y hlt))
            | inr heq =>
              have heq' : y = M := heq
              rw [heq'] at hM_lt_y
              exact False.elim (lt_irrefl M hM_lt_y)
          · left
            intro x hx
            exact hEmpty ⟨x, hx⟩
        | finite val =>
          intro hBounded
          by_cases hEmpty : (openInterval (Endpoint.finite val) Endpoint.posInf).Nonempty
          · obtain ⟨x0, hx0left, hx0right⟩ := hEmpty
            rcases hBounded with ⟨M, hM_upper⟩
            obtain ⟨y, hym⟩ := exists_gt (max1 M (Power.coord1 x0))
            have hM_lt_y : LT.lt M y := by
              by_cases h : LT.lt M (Power.coord1 x0)
              · have hmax : max1 M (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if LT.lt M (Power.coord1 x0) then Power.coord1 x0 else M)
                    = Power.coord1 x0
                  rw [if_pos h]
                rw [hmax] at hym
                exact lt_trans h hym
              · have hmax : max1 M (Power.coord1 x0) = M := by
                  show (if LT.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                  rw [if_neg h]
                rw [hmax] at hym
                exact hym
            have hx0_gt_a : LT.lt val (Power.coord1 x0) := hx0left
            have hz_gt_a : Endpoint.lt (Endpoint.finite val) (Endpoint.finite y) := by
              by_cases h : LT.lt M (Power.coord1 x0)
              · have hmax : max1 M (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if LT.lt M (Power.coord1 x0) then Power.coord1 x0 else M)
                    = Power.coord1 x0
                  rw [if_pos h]
                rw [hmax] at hym
                exact lt_trans hx0_gt_a hym
              · have hmin_le : LT.lt (Power.coord1 x0) M ∨ Power.coord1 x0 = M := by
                  rcases lt_trichotomy (Power.coord1 x0) M with h1 | h2 | h3
                  · exact Or.inl h1
                  · exact Or.inr h2
                  · exact absurd h3 h
                cases hmin_le with
                | inl hlt =>
                  have hmax : max1 M (Power.coord1 x0) = M := by
                    show (if LT.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                    rw [if_neg h]
                  rw [hmax] at hym
                  exact lt_trans (lt_trans hx0_gt_a hlt) hym
                | inr heq =>
                  have hmax : max1 M (Power.coord1 x0) = M := by
                    show (if LT.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                    rw [if_neg h]
                  rw [hmax] at hym
                  rw [heq] at hx0_gt_a
                  exact lt_trans hx0_gt_a hym
            let y_pow : Power R 1 := fun _ => y
            have hy_in : openInterval (Endpoint.finite val) Endpoint.posInf y_pow :=
              ⟨hz_gt_a, trivial⟩
            have hy_le_M := hM_upper y_pow hy_in
            cases hy_le_M with
            | inl hlt =>
              exact False.elim (lt_irrefl M (lt_trans hM_lt_y hlt))
            | inr heq =>
              have heq' : y = M := heq
              rw [heq'] at hM_lt_y
              exact False.elim (lt_irrefl M hM_lt_y)
          · left
            intro x hx
            exact hEmpty ⟨x, hx⟩
        | posInf =>
          intro _
          left
          intro x hx
          exact hx.left
    | union =>
      rename_i A B hFA hFB ihA ihB
      intro hBounded
      have hBoundA : BoundedAbove1 A := by
        rcases hBounded with ⟨b0, hb0⟩
        exact ⟨b0, fun x hx => hb0 x (Or.inl hx)⟩
      have hBoundB : BoundedAbove1 B := by
        rcases hBounded with ⟨b0, hb0⟩
        exact ⟨b0, fun x hx => hb0 x (Or.inr hx)⟩
      have hResA := ihA hBoundA
      have hResB := ihB hBoundB
      cases hResA with
      | inl hEmptyA =>
        cases hResB with
        | inl hEmptyB =>
          left
          intro x hx
          cases hx with
          | inl hxA => exact hEmptyA x hxA
          | inr hxB => exact hEmptyB x hxB
        | inr hSupB =>
          right
          rcases hSupB with ⟨sB, hsB_upper, hsB_least⟩
          use sB
          constructor
          · intro x hx
            cases hx with
            | inl hxA => exact False.elim (hEmptyA x hxA)
            | inr hxB => exact hsB_upper x hxB
          · intro b hb
            have hbB : IsUpperBound1 B b := fun x hx => hb x (Or.inr hx)
            exact hsB_least b hbB
      | inr hSupA =>
        cases hResB with
        | inl hEmptyB =>
          right
          rcases hSupA with ⟨sA, hsA_upper, hsA_least⟩
          use sA
          constructor
          · intro x hx
            cases hx with
            | inl hxA => exact hsA_upper x hxA
            | inr hxB => exact False.elim (hEmptyB x hxB)
          · intro b hb
            have hbA : IsUpperBound1 A b := fun x hx => hb x (Or.inl hx)
            exact hsA_least b hbA
        | inr hSupB =>
          right
          rcases hSupA with ⟨sA, hsA⟩
          rcases hSupB with ⟨sB, hsB⟩
          use max1 sA sB
          exact supUnionAux A B sA sB hsA hsB
  cases hCore A hDef hBounded with
  | inl hEmpty =>
    rcases hNotEmpty with ⟨x, hx⟩
    exact False.elim (hEmpty x hx)
  | inr hSup =>
    exact hSup

namespace Monotonicity_Theorem

-- Restriction of a definable function to a definable subset of its domain.
theorem restrictDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {M : OMinimalStructure R} {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (A' : Set (Power R 1)) (hA' : M.S 1 A') (hsub : A'.Subset I) :
    ∃ f' : DefinableFunction M A' B,
      ∀ x (hx' : A' x), f'.toFun (Subtype.mk x hx') = f.toFun (Subtype.mk x (hsub hx')) := by
  refine ⟨⟨hA', f.codomain_mem, (fun x => f.toFun ⟨x.1, hsub x.2⟩), ?_⟩, fun x hx' => rfl⟩
  have heq : FunctionGraph (fun x : {x : Power R 1 // A' x} => f.toFun ⟨x.1, hsub x.2⟩)
      = ({z : Power R (1 + 1) | A' (Power.left z)} ∩
        (FunctionGraph f.toFun)) := by
    funext z
    apply propext
    constructor
    · intro h
      obtain ⟨hx', heq0⟩ := h
      refine ⟨hx', ?_⟩
      exact ⟨hsub hx', heq0⟩
    · intro h
      obtain ⟨ha', hx, heq0⟩ := h
      refine ⟨ha', ?_⟩
      have hrfl : (f.toFun ⟨Power.left z, hsub ha'⟩).1 = (f.toFun ⟨Power.left z, hx⟩).1 := rfl
      rw [hrfl]
      exact heq0
  rw [heq]
  exact M.inter_mem (M.reindex_mem (Fin.castAdd 1) hA') f.graph_mem

-- A nonempty open interval with finite endpoints is infinite.
-- Proof by induction on the putative coordinate list: removing the (unique)
-- point with a given coordinate splits the interval into two smaller ones.
theorem intervalInfiniteAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] :
    ∀ (L : List R) (u v : R), LT.lt u v →
      (∀ x : Power R 1, openInterval (Endpoint.finite u) (Endpoint.finite v) x →
        Power.coord1 x ∈ L) → False := by
  intro L
  induction L with
  | nil =>
    intro u v huv hsub
    obtain ⟨r, hr1, hr2⟩ := exists_between huv
    have hmem : Power.coord1 (fun _ => r) ∈ ([] : List R) :=
      hsub (fun _ => r) ⟨hr1, hr2⟩
    simp at hmem
  | cons c cs ih =>
    intro u v huv hsub
    obtain ⟨r, hr1, hr2⟩ := exists_between huv
    have hrL : r ∈ c :: cs := hsub (fun _ => r) ⟨hr1, hr2⟩
    by_cases hc : ∃ p : Power R 1, openInterval (Endpoint.finite u) (Endpoint.finite v) p ∧
        Power.coord1 p = c
    · obtain ⟨p, hpJ, hpc⟩ := hc
      have hupc : LT.lt u (Power.coord1 p) := hpJ.left
      have hpcv : LT.lt (Power.coord1 p) v := hpJ.right
      have hleft : ∀ x : Power R 1, openInterval (Endpoint.finite u)
          (Endpoint.finite (Power.coord1 p)) x → Power.coord1 x ∈ cs := by
        intro x hx
        have hxJ : openInterval (Endpoint.finite u) (Endpoint.finite v) x :=
          ⟨hx.left, lt_trans hx.right hpcv⟩
        have hmem := hsub x hxJ
        obtain h | h := List.mem_cons.mp hmem
        · have : x = p := ptEqAux (by rw [h, hpc])
          have hx2 : LT.lt (Power.coord1 x) (Power.coord1 p) := hx.right
          have hcon : LT.lt (Power.coord1 p) (Power.coord1 p) := this ▸ hx2
          exact False.elim (lt_irrefl _ hcon)
        · exact h
      exact ih u (Power.coord1 p) hupc hleft
    · apply ih u v huv
      intro x hx
      have hmem := hsub x hx
      obtain h | h := List.mem_cons.mp hmem
      · exfalso
        apply hc
        exact ⟨x, hx, h⟩
      · exact h

namespace Monotonicity_Theorem

-- Index maps for the constancy-failure matrix.
-- Tuple layout (arity 6): 0:u, 1:v, 2:p, 3:q, 4:wp, 5:wq.
def cIp : Fin 1 → Fin 6 := fun _ => ⟨2, by decide⟩
def cIq : Fin 1 → Fin 6 := fun _ => ⟨3, by decide⟩
def cLTup : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
def cLTpv : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨1, by decide⟩
def cLTuq : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩
def cLTqv : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨3, by decide⟩ else ⟨1, by decide⟩
def cGp : Fin (1 + 1) → Fin 6 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨4, by decide⟩
def cGq : Fin (1 + 1) → Fin 6 := fun j => if _ : j.val = 0 then ⟨3, by decide⟩ else ⟨5, by decide⟩
-- Window-position maps over (x, u, v) : Fin 3.
def wLTux : Fin 2 → Fin 3 := fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩
def wLTxv : Fin 2 → Fin 3 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩

end Monotonicity_Theorem

open Monotonicity_Theorem

-- Lambda-form non-equality is definable (Fin 1 funext both ways).
theorem lambdaNeqDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) :
    M.S 6 (fun t : Power R 6 => ¬ ((fun _ : Fin 1 => t (⟨4, by decide⟩ : Fin 6)) =
      (fun _ : Fin 1 => t (⟨5, by decide⟩ : Fin 6)))) := by
  have heq : (fun t : Power R 6 => ¬ ((fun _ : Fin 1 => t (⟨4, by decide⟩ : Fin 6)) =
      (fun _ : Fin 1 => t (⟨5, by decide⟩ : Fin 6)))) =
      (fun t : Power R 6 => ¬ t (⟨4, by decide⟩ : Fin 6) = t (⟨5, by decide⟩ : Fin 6)) := by
    funext t
    apply propext
    constructor
    · intro h hcon
      apply h
      funext i
      exact hcon
    · intro h hcon
      apply h
      exact congrFun hcon ⟨0, by decide⟩
  rw [heq]
  exact M.compl_mem (M.diagonal_mem (⟨4, by decide⟩ : Fin 6)
    (⟨5, by decide⟩ : Fin 6) (by decide))

-- Lambda-form equality is definable.
theorem lambdaEqDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) :
    M.S 6 (fun t : Power R 6 => ((fun _ : Fin 1 => t (⟨4, by decide⟩ : Fin 6)) =
      (fun _ : Fin 1 => t (⟨5, by decide⟩ : Fin 6)))) := by
  have heq : (fun t : Power R 6 => ((fun _ : Fin 1 => t (⟨4, by decide⟩ : Fin 6)) =
      (fun _ : Fin 1 => t (⟨5, by decide⟩ : Fin 6)))) =
      (fun t : Power R 6 => t (⟨4, by decide⟩ : Fin 6) = t (⟨5, by decide⟩ : Fin 6)) := by
    funext t
    apply propext
    constructor
    · intro h
      exact congrFun h ⟨0, by decide⟩
    · intro h
      funext i
      exact h
  rw [heq]
  exact M.diagonal_mem (⟨4, by decide⟩ : Fin 6)
    (⟨5, by decide⟩ : Fin 6) (by decide)

-- Points with a constant window form a definable class.
-- (Witnesses are coordinates, so the bridge proof is definitional.)
theorem constClassDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (lo hi : R) :
    M.S 1 (fun x : Power R 1 => openInterval (Endpoint.finite lo) (Endpoint.finite hi) x ∧
      I x ∧
      (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
          openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
  have hF : M.S 6 (fun q : Power R 6 =>
      I (fun i : Fin 1 => q (cIp i)) ∧
      I (fun i : Fin 1 => q (cIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (cLTup j)) 0) ((fun j : Fin 2 => q (cLTup j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (cLTpv j)) 0) ((fun j : Fin 2 => q (cLTpv j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (cLTuq j)) 0) ((fun j : Fin 2 => q (cLTuq j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (cLTqv j)) 0) ((fun j : Fin 2 => q (cLTqv j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (cGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (cGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨4, by decide⟩ : Fin 6)) =
        (fun _ : Fin 1 => q (⟨5, by decide⟩ : Fin 6)))) :=
    M.inter_mem (M.reindex_mem cIp f.domain_mem)
      (M.inter_mem (M.reindex_mem cIq f.domain_mem)
        (M.inter_mem (M.reindex_mem cLTup M.lt_mem)
          (M.inter_mem (M.reindex_mem cLTpv M.lt_mem)
            (M.inter_mem (M.reindex_mem cLTuq M.lt_mem)
              (M.inter_mem (M.reindex_mem cLTqv M.lt_mem)
                (M.inter_mem (M.reindex_mem cGp f.graph_mem)
                  (M.inter_mem (M.reindex_mem cGq f.graph_mem)
                    (lambdaNeqDefinable M))))))))
  have hF7 : M.S (3 + 4) (fun q : Power R (3 + 4) =>
      (fun t : Power R 6 =>
        I (fun i : Fin 1 => t (cIp i)) ∧
        I (fun i : Fin 1 => t (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t (cLTup j)) 0) ((fun j : Fin 2 => t (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTpv j)) 0) ((fun j : Fin 2 => t (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTuq j)) 0) ((fun j : Fin 2 => t (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTqv j)) 0) ((fun j : Fin 2 => t (cLTqv j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t (cGq j)) ∧
        ¬ ((fun _ : Fin 1 => t (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => q (Fin.succ i))) :=
    M.reindex_mem Fin.succ hF
  have hProj : M.S 3 (fun y : Power R 3 => ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        ¬ ((fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))) :=
    M.existsLast_mem hF7
  have hC : M.S 3 (fun y : Power R 3 => ¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        ¬ ((fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))) :=
    M.compl_mem hProj
  have hWIN : M.S 3 (fun y : Power R 3 =>
      LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) :=
    M.inter_mem (M.reindex_mem wLTux M.lt_mem) (M.reindex_mem wLTxv M.lt_mem)
  have hC3 : M.S 3 (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        ¬ ((fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i)))) :=
    M.inter_mem hWIN hC
  have hC1 : M.S 1 (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        ¬ ((fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w)) :=
    M.existsLast_mem (n := 1) (m := 2) hC3
  have hJmem : M.S 1 (openInterval (Endpoint.finite lo) (Endpoint.finite hi)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hCfin : M.S 1 (((openInterval (Endpoint.finite lo) (Endpoint.finite hi)) ∩ I)
      ∩ (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        ¬ ((fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w))) :=
    M.inter_mem (M.inter_mem hJmem f.domain_mem) hC1
  have heqC : (((openInterval (Endpoint.finite lo) (Endpoint.finite hi)) ∩ I)
      ∩ (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        ¬ ((fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w)))
      = (fun x : Power R 1 => openInterval (Endpoint.finite lo) (Endpoint.finite hi) x ∧
        I x ∧
        (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
          ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
            openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
            openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => pc) (fun _ => wpc)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => qc) (fun _ => wqc)) ∧
            ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
    funext x
    apply propext
    constructor
    · intro h
      obtain ⟨⟨hJy, hI⟩, w, hWINw, hNEG⟩ := h
      refine ⟨hJy, hI, (w (⟨0, by decide⟩ : Fin 2)), (w (⟨1, by decide⟩ : Fin 2)), ?_, ?_, ?_⟩
      · exact hWINw.left
      · exact hWINw.right
      · intro hex
        apply hNEG
        obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hGp, hGq, hne⟩ := hex
        refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
          else if k = (⟨1, by decide⟩ : Fin 4) then qc
          else if k = (⟨2, by decide⟩ : Fin 4) then wpc
          else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact hJp.left
        · exact hJp.right
        · exact hJq.left
        · exact hJq.right
        · have eGp : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x w)
              (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
              else if k = (⟨1, by decide⟩ : Fin 4) then qc
              else if k = (⟨2, by decide⟩ : Fin 4) then wpc
              else wqc)) (Fin.succ i)) (cGp j))
            = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x w)
              (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
              else if k = (⟨1, by decide⟩ : Fin 4) then qc
              else if k = (⟨2, by decide⟩ : Fin 4) then wpc
              else wqc)) (Fin.succ i)) (cGq j))
            = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [eGq]
          exact hGq
        · exact hne
    · intro h
      obtain ⟨hJy, hI, u, v, hux, hxv, hNEG⟩ := h
      refine ⟨⟨hJy, hI⟩, (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
        else v), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · exact hux
        · exact hxv
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hGp, hGq, hne⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · have eGp : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x
              (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
              else v)) t) (Fin.succ i)) (cGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x
              (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
              else v)) t) (Fin.succ i)) (cGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · exact hne
  rw [← heqC]
  exact hCfin

-- Index maps for the increasing-failure matrix (same layout, plus p<q and value-BAD).
def uLTpq : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨3, by decide⟩
def uLTbad : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨5, by decide⟩ else ⟨4, by decide⟩

-- Points with a strictly increasing window form a definable class.
theorem incClassDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (lo hi : R) :
    M.S 1 (fun x : Power R 1 => openInterval (Endpoint.finite lo) (Endpoint.finite hi) x ∧
      I x ∧
      (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
          openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
          LT.lt pc qc ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
            ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))))) := by
  have hF : M.S 6 (fun q : Power R 6 =>
      I (fun i : Fin 1 => q (Monotonicity_Theorem.cIp i)) ∧
      I (fun i : Fin 1 => q (Monotonicity_Theorem.cIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTup j)) 0)
        ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTup j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTpv j)) 0)
        ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTpv j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTuq j)) 0)
        ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTuq j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTqv j)) 0)
        ((fun j : Fin 2 => q (Monotonicity_Theorem.cLTqv j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (uLTpq j)) 0)
        ((fun j : Fin 2 => q (uLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (Monotonicity_Theorem.cGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (Monotonicity_Theorem.cGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (uLTbad j)) 0)
        ((fun j : Fin 2 => q (uLTbad j)) 1) ∨
      (fun _ : Fin 1 => q (⟨4, by decide⟩ : Fin 6)) =
        (fun _ : Fin 1 => q (⟨5, by decide⟩ : Fin 6)))) :=
    M.inter_mem (M.reindex_mem Monotonicity_Theorem.cIp f.domain_mem)
      (M.inter_mem (M.reindex_mem Monotonicity_Theorem.cIq f.domain_mem)
        (M.inter_mem (M.reindex_mem Monotonicity_Theorem.cLTup M.lt_mem)
          (M.inter_mem (M.reindex_mem Monotonicity_Theorem.cLTpv M.lt_mem)
            (M.inter_mem (M.reindex_mem Monotonicity_Theorem.cLTuq M.lt_mem)
              (M.inter_mem (M.reindex_mem Monotonicity_Theorem.cLTqv M.lt_mem)
                (M.inter_mem (M.reindex_mem uLTpq M.lt_mem)
                    (M.inter_mem (M.reindex_mem Monotonicity_Theorem.cGp f.graph_mem)
                      (M.inter_mem (M.reindex_mem Monotonicity_Theorem.cGq f.graph_mem)
                        (M.union_mem (M.reindex_mem uLTbad M.lt_mem)
                          (lambdaEqDefinable M))))))))))
  have hF7 : M.S (3 + 4) (fun q : Power R (3 + 4) =>
      (fun t : Power R 6 =>
        I (fun i : Fin 1 => t (cIp i)) ∧
        I (fun i : Fin 1 => t (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t (cLTup j)) 0) ((fun j : Fin 2 => t (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTpv j)) 0) ((fun j : Fin 2 => t (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTuq j)) 0) ((fun j : Fin 2 => t (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTqv j)) 0) ((fun j : Fin 2 => t (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (uLTpq j)) 0) ((fun j : Fin 2 => t (uLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t (uLTbad j)) 0) ((fun j : Fin 2 => t (uLTbad j)) 1) ∨
        (fun _ : Fin 1 => t (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => q (Fin.succ i))) :=
    M.reindex_mem Fin.succ hF
  have hProj : M.S 3 (fun y : Power R 3 => ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (uLTpq j)) 0) ((fun j : Fin 2 => t6 (uLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (uLTbad j)) 0) ((fun j : Fin 2 => t6 (uLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))) :=
    M.existsLast_mem hF7
  have hC : M.S 3 (fun y : Power R 3 => ¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (uLTpq j)) 0) ((fun j : Fin 2 => t6 (uLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (uLTbad j)) 0) ((fun j : Fin 2 => t6 (uLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))) :=
    M.compl_mem hProj
  have hWIN : M.S 3 (fun y : Power R 3 =>
      LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) :=
    M.inter_mem (M.reindex_mem wLTux M.lt_mem) (M.reindex_mem wLTxv M.lt_mem)
  have hC3 : M.S 3 (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (uLTpq j)) 0) ((fun j : Fin 2 => t6 (uLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (uLTbad j)) 0) ((fun j : Fin 2 => t6 (uLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i)))) :=
    M.inter_mem hWIN hC
  have hC1 : M.S 1 (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (uLTpq j)) 0) ((fun j : Fin 2 => t6 (uLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (uLTbad j)) 0) ((fun j : Fin 2 => t6 (uLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w)) :=
    M.existsLast_mem (n := 1) (m := 2) hC3
  have hJmem : M.S 1 (openInterval (Endpoint.finite lo) (Endpoint.finite hi)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hCfin : M.S 1 (((openInterval (Endpoint.finite lo) (Endpoint.finite hi)) ∩ I)
      ∩ (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (uLTpq j)) 0) ((fun j : Fin 2 => t6 (uLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (uLTbad j)) 0) ((fun j : Fin 2 => t6 (uLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w))) :=
    M.inter_mem (M.inter_mem hJmem f.domain_mem) hC1
  have heqU : (((openInterval (Endpoint.finite lo) (Endpoint.finite hi)) ∩ I)
      ∩ (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (uLTpq j)) 0) ((fun j : Fin 2 => t6 (uLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (uLTbad j)) 0) ((fun j : Fin 2 => t6 (uLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w)))
      = (fun x : Power R 1 => openInterval (Endpoint.finite lo) (Endpoint.finite hi) x ∧
        I x ∧
        (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
          ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
            openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
            openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
            LT.lt pc qc ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => pc) (fun _ => wpc)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => qc) (fun _ => wqc)) ∧
            (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
              ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))))) := by
    funext x
    apply propext
    constructor
    · intro h
      obtain ⟨⟨hJy, hI⟩, w, hWINw, hNEG⟩ := h
      refine ⟨hJy, hI, (w (⟨0, by decide⟩ : Fin 2)), (w (⟨1, by decide⟩ : Fin 2)), ?_, ?_, ?_⟩
      · exact hWINw.left
      · exact hWINw.right
      · intro hex
        apply hNEG
        obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hPq, hGp, hGq, hBAD⟩ := hex
        refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
          else if k = (⟨1, by decide⟩ : Fin 4) then qc
          else if k = (⟨2, by decide⟩ : Fin 4) then wpc
          else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact hJp.left
        · exact hJp.right
        · exact hJq.left
        · exact hJq.right
        · exact hPq
        · have eGp : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x w)
              (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
              else if k = (⟨1, by decide⟩ : Fin 4) then qc
              else if k = (⟨2, by decide⟩ : Fin 4) then wpc
              else wqc)) (Fin.succ i)) (cGp j))
            = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x w)
              (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
              else if k = (⟨1, by decide⟩ : Fin 4) then qc
              else if k = (⟨2, by decide⟩ : Fin 4) then wpc
              else wqc)) (Fin.succ i)) (cGq j))
            = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [eGq]
          exact hGq
        · rcases hBAD with hBADlt | hBADeq
          · exact Or.inl hBADlt
          · exact Or.inr hBADeq
    · intro h
      obtain ⟨hJy, hI, u, v, hux, hxv, hNEG⟩ := h
      refine ⟨⟨hJy, hI⟩, (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
        else v), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · exact hux
        · exact hxv
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hPq, hGp, hGq, hBAD⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hPq
        · have eGp : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x
              (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
              else v)) t) (Fin.succ i)) (cGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x
              (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
              else v)) t) (Fin.succ i)) (cGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · rcases hBAD with hBADlt | hBADeq
          · exact Or.inl hBADlt
          · exact Or.inr hBADeq
  rw [← heqU]
  exact hCfin

-- Index maps for the decreasing-failure matrix (same layout; BAD is wp<wq).
def dLTpq : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨3, by decide⟩
def dLTbad : Fin 2 → Fin 6 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨5, by decide⟩

-- Points with a strictly decreasing window form a definable class.
theorem decClassDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (lo hi : R) :
    M.S 1 (fun x : Power R 1 => openInterval (Endpoint.finite lo) (Endpoint.finite hi) x ∧
      I x ∧
      (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
          openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
          LT.lt pc qc ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
            ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))))) := by
  have hF : M.S 6 (fun q : Power R 6 =>
      I (fun i : Fin 1 => q (cIp i)) ∧
      I (fun i : Fin 1 => q (cIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (cLTup j)) 0)
        ((fun j : Fin 2 => q (cLTup j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (cLTpv j)) 0)
        ((fun j : Fin 2 => q (cLTpv j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (cLTuq j)) 0)
        ((fun j : Fin 2 => q (cLTuq j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (cLTqv j)) 0)
        ((fun j : Fin 2 => q (cLTqv j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dLTpq j)) 0)
        ((fun j : Fin 2 => q (dLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (cGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (cGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (dLTbad j)) 0)
        ((fun j : Fin 2 => q (dLTbad j)) 1) ∨
      (fun _ : Fin 1 => q (⟨4, by decide⟩ : Fin 6)) =
        (fun _ : Fin 1 => q (⟨5, by decide⟩ : Fin 6)))) :=
    M.inter_mem (M.reindex_mem cIp f.domain_mem)
      (M.inter_mem (M.reindex_mem cIq f.domain_mem)
        (M.inter_mem (M.reindex_mem cLTup M.lt_mem)
          (M.inter_mem (M.reindex_mem cLTpv M.lt_mem)
            (M.inter_mem (M.reindex_mem cLTuq M.lt_mem)
              (M.inter_mem (M.reindex_mem cLTqv M.lt_mem)
                (M.inter_mem (M.reindex_mem dLTpq M.lt_mem)
                    (M.inter_mem (M.reindex_mem cGp f.graph_mem)
                      (M.inter_mem (M.reindex_mem cGq f.graph_mem)
                        (M.union_mem (M.reindex_mem dLTbad M.lt_mem)
                          (lambdaEqDefinable M))))))))))
  have hF7 : M.S (3 + 4) (fun q : Power R (3 + 4) =>
      (fun t : Power R 6 =>
        I (fun i : Fin 1 => t (cIp i)) ∧
        I (fun i : Fin 1 => t (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t (cLTup j)) 0) ((fun j : Fin 2 => t (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTpv j)) 0) ((fun j : Fin 2 => t (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTuq j)) 0) ((fun j : Fin 2 => t (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (cLTqv j)) 0) ((fun j : Fin 2 => t (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t (dLTpq j)) 0) ((fun j : Fin 2 => t (dLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t (dLTbad j)) 0) ((fun j : Fin 2 => t (dLTbad j)) 1) ∨
        (fun _ : Fin 1 => t (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => q (Fin.succ i))) :=
    M.reindex_mem Fin.succ hF
  have hProj : M.S 3 (fun y : Power R 3 => ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (dLTpq j)) 0) ((fun j : Fin 2 => t6 (dLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (dLTbad j)) 0) ((fun j : Fin 2 => t6 (dLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))) :=
    M.existsLast_mem hF7
  have hC : M.S 3 (fun y : Power R 3 => ¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (dLTpq j)) 0) ((fun j : Fin 2 => t6 (dLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (dLTbad j)) 0) ((fun j : Fin 2 => t6 (dLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))) :=
    M.compl_mem hProj
  have hWIN : M.S 3 (fun y : Power R 3 =>
      LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) :=
    M.inter_mem (M.reindex_mem wLTux M.lt_mem) (M.reindex_mem wLTxv M.lt_mem)
  have hC3 : M.S 3 (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (dLTpq j)) 0) ((fun j : Fin 2 => t6 (dLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (dLTbad j)) 0) ((fun j : Fin 2 => t6 (dLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i)))) :=
    M.inter_mem hWIN hC
  have hC1 : M.S 1 (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (dLTpq j)) 0) ((fun j : Fin 2 => t6 (dLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (dLTbad j)) 0) ((fun j : Fin 2 => t6 (dLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w)) :=
    M.existsLast_mem (n := 1) (m := 2) hC3
  have hJmem : M.S 1 (openInterval (Endpoint.finite lo) (Endpoint.finite hi)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hCfin : M.S 1 (((openInterval (Endpoint.finite lo) (Endpoint.finite hi)) ∩ I)
      ∩ (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (dLTpq j)) 0) ((fun j : Fin 2 => t6 (dLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (dLTbad j)) 0) ((fun j : Fin 2 => t6 (dLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w))) :=
    M.inter_mem (M.inter_mem hJmem f.domain_mem) hC1
  have heqD : (((openInterval (Endpoint.finite lo) (Endpoint.finite hi)) ∩ I)
      ∩ (fun x : Power R 1 => ∃ w : Power R 2,
      (fun y : Power R 3 =>
      (LT.lt ((fun j : Fin 2 => y (wLTux j)) 0) ((fun j : Fin 2 => y (wLTux j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wLTxv j)) 0) ((fun j : Fin 2 => y (wLTxv j)) 1)) ∧
      (¬ ∃ t : Power R 4,
      (fun t6 : Power R 6 =>
        I (fun i : Fin 1 => t6 (cIp i)) ∧
        I (fun i : Fin 1 => t6 (cIq i)) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTup j)) 0) ((fun j : Fin 2 => t6 (cLTup j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTpv j)) 0) ((fun j : Fin 2 => t6 (cLTpv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTuq j)) 0) ((fun j : Fin 2 => t6 (cLTuq j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (cLTqv j)) 0) ((fun j : Fin 2 => t6 (cLTqv j)) 1) ∧
        LT.lt ((fun j : Fin 2 => t6 (dLTpq j)) 0) ((fun j : Fin 2 => t6 (dLTpq j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGp j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => t6 (cGq j)) ∧
        (LT.lt ((fun j : Fin 2 => t6 (dLTbad j)) 0) ((fun j : Fin 2 => t6 (dLTbad j)) 1) ∨
        (fun _ : Fin 1 => t6 (⟨4, by decide⟩ : Fin 6)) =
          (fun _ : Fin 1 => t6 (⟨5, by decide⟩ : Fin 6))))
        (fun i : Fin 6 => (Power.append y t) (Fin.succ i))))
      (Power.append x w)))
      = (fun x : Power R 1 => openInterval (Endpoint.finite lo) (Endpoint.finite hi) x ∧
        I x ∧
        (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
          ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
            openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
            openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
            LT.lt pc qc ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => pc) (fun _ => wpc)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => qc) (fun _ => wqc)) ∧
            (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
              ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))))) := by
    funext x
    apply propext
    constructor
    · intro h
      obtain ⟨⟨hJy, hI⟩, w, hWINw, hNEG⟩ := h
      refine ⟨hJy, hI, (w (⟨0, by decide⟩ : Fin 2)), (w (⟨1, by decide⟩ : Fin 2)), ?_, ?_, ?_⟩
      · exact hWINw.left
      · exact hWINw.right
      · intro hex
        apply hNEG
        obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hPq, hGp, hGq, hBAD⟩ := hex
        refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
          else if k = (⟨1, by decide⟩ : Fin 4) then qc
          else if k = (⟨2, by decide⟩ : Fin 4) then wpc
          else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact hJp.left
        · exact hJp.right
        · exact hJq.left
        · exact hJq.right
        · exact hPq
        · have eGp : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x w)
              (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
              else if k = (⟨1, by decide⟩ : Fin 4) then qc
              else if k = (⟨2, by decide⟩ : Fin 4) then wpc
              else wqc)) (Fin.succ i)) (cGp j))
            = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x w)
              (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
              else if k = (⟨1, by decide⟩ : Fin 4) then qc
              else if k = (⟨2, by decide⟩ : Fin 4) then wpc
              else wqc)) (Fin.succ i)) (cGq j))
            = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [eGq]
          exact hGq
        · rcases hBAD with hBADlt | hBADeq
          · exact Or.inl hBADlt
          · exact Or.inr hBADeq
    · intro h
      obtain ⟨hJy, hI, u, v, hux, hxv, hNEG⟩ := h
      refine ⟨⟨hJy, hI⟩, (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
        else v), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · exact hux
        · exact hxv
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hPq, hGp, hGq, hBAD⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hPq
        · have eGp : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x
              (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
              else v)) t) (Fin.succ i)) (cGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (fun i : Fin 6 => (Power.append (Power.append x
              (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then u
              else v)) t) (Fin.succ i)) (cGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · rcases hBAD with hBADlt | hBADeq
          · exact Or.inl hBADlt
          · exact Or.inr hBADeq
  rw [← heqD]
  exact hCfin

namespace Monotonicity_Theorem

end Monotonicity_Theorem

open Monotonicity_Theorem

-- A nonempty open interval contains a finite-endpoint subwindow.
theorem finiteSubwindowAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {c d : Endpoint R} {p : Power R 1} (hp : openInterval c d p) :
    ∃ u v : R, LT.lt u v ∧
      (∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
        openInterval c d x) := by
  obtain ⟨hpc, hpd⟩ := hp
  have hu : ∃ u : R, Endpoint.lt c (Endpoint.finite u) ∧ LT.lt u (Power.coord1 p) := by
    cases c with
    | negInf =>
      obtain ⟨y, hym⟩ := exists_lt (Power.coord1 p)
      exact ⟨y, trivial, hym⟩
    | finite val =>
      have hpc' : LT.lt val (Power.coord1 p) := hpc
      obtain ⟨y, hy1, hy2⟩ := exists_between hpc'
      exact ⟨y, hy1, hy2⟩
    | posInf => exact False.elim hpc
  have hv : ∃ v : R, LT.lt (Power.coord1 p) v ∧ Endpoint.lt (Endpoint.finite v) d := by
    cases d with
    | negInf => exact False.elim hpd
    | finite val =>
      have hpd' : LT.lt (Power.coord1 p) val := hpd
      obtain ⟨y, hy1, hy2⟩ := exists_between hpd'
      exact ⟨y, hy1, hy2⟩
    | posInf =>
      obtain ⟨y, hym⟩ := exists_gt (Power.coord1 p)
      exact ⟨y, hym, trivial⟩
  obtain ⟨u, hcu, hup⟩ := hu
  obtain ⟨v, hpv, hvd⟩ := hv
  refine ⟨u, v, lt_trans hup hpv, ?_⟩
  intro x hx
  obtain ⟨hxu, hxv⟩ := hx
  have hleft : Endpoint.lt c (Endpoint.finite (Power.coord1 x)) := by
    cases c with
    | negInf => exact trivial
    | finite val => exact lt_trans hcu hxu
    | posInf => exact False.elim hcu
  have hright : Endpoint.lt (Endpoint.finite (Power.coord1 x)) d := by
    cases d with
    | negInf => exact False.elim hvd
    | finite val => exact lt_trans hxv hvd
    | posInf => exact trivial
  exact ⟨hleft, hright⟩

-- FunctionGraph witnesses give values.
theorem graphValAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {M : OMinimalStructure R} {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (p' wp' : Power R 1) (hI : I p')
    (hG : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
      (Power.append p' wp')) :
    Power.coord1 wp' = Power.coord1 ((f.toFun (Subtype.mk p' hI)).1) := by
  obtain ⟨hx0, heq0⟩ := hG
  have eL : Power.left (Power.append p' wp') = p' := appendLeftAux _ _
  have eR : Power.right (Power.append p' wp') = wp' := appendRightAux _ _
  have heq1 : wp' = (f.toFun (Subtype.mk p' hI)).1 := by
    calc wp' = Power.right (Power.append p' wp') := eR.symm
      _ = (f.toFun (Subtype.mk (Power.left (Power.append p' wp')) hx0)).1 := heq0
      _ = (f.toFun (Subtype.mk p' hI)).1 := by simp only [eL]
  rw [heq1]

-- Shrink an endpoint-window around a point to finite coordinates inside it.
theorem shrinkWindowAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {c d : Endpoint R} {z : Power R 1} (hz : openInterval c d z) :
    ∃ u v : R, LT.lt u (Power.coord1 z) ∧ LT.lt (Power.coord1 z) v ∧
      (∀ w, openInterval (Endpoint.finite u) (Endpoint.finite v) w ->
        openInterval c d w) := by
  obtain ⟨hzc, hzd⟩ := hz
  have hu : ∃ u : R, Endpoint.lt c (Endpoint.finite u) ∧ LT.lt u (Power.coord1 z) := by
    cases c with
    | negInf =>
      obtain ⟨y, hym⟩ := exists_lt (Power.coord1 z)
      exact ⟨y, trivial, hym⟩
    | finite val =>
      have hzc' : LT.lt val (Power.coord1 z) := hzc
      obtain ⟨y, hy1, hy2⟩ := exists_between hzc'
      exact ⟨y, hy1, hy2⟩
    | posInf => exact False.elim hzc
  have hv : ∃ v : R, LT.lt (Power.coord1 z) v ∧ Endpoint.lt (Endpoint.finite v) d := by
    cases d with
    | negInf => exact False.elim hzd
    | finite val =>
      have hzd' : LT.lt (Power.coord1 z) val := hzd
      obtain ⟨y, hy1, hy2⟩ := exists_between hzd'
      exact ⟨y, hy1, hy2⟩
    | posInf =>
      obtain ⟨y, hym⟩ := exists_gt (Power.coord1 z)
      exact ⟨y, hym, trivial⟩
  obtain ⟨u, hcu, huz⟩ := hu
  obtain ⟨v, hzv, hvd⟩ := hv
  refine ⟨u, v, huz, hzv, ?_⟩
  intro w hw
  obtain ⟨hwu, hwv⟩ := hw
  have hleft : Endpoint.lt c (Endpoint.finite (Power.coord1 w)) := by
    cases c with
    | negInf => exact trivial
    | finite val => exact lt_trans hcu hwu
    | posInf => exact False.elim hcu
  have hright : Endpoint.lt (Endpoint.finite (Power.coord1 w)) d := by
    cases d with
    | negInf => exact False.elim hvd
    | finite val => exact lt_trans hwv hvd
    | posInf => exact trivial
  exact ⟨hleft, hright⟩

-- A window strictly between endpoints is nonempty (with fallback for doubly-infinite).
theorem nonemptyWinAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {c d : Endpoint R} (hlt : Endpoint.lt c d) (p₀ : Power R 1) :
    (openInterval c d).Nonempty := by
  cases c with
  | negInf =>
    cases d with
    | negInf => exact False.elim hlt
    | finite val =>
      obtain ⟨y, hym⟩ := exists_lt val
      exact ⟨fun _ => y, trivial, hym⟩
    | posInf => exact ⟨p₀, trivial, trivial⟩
  | finite val =>
    cases d with
    | negInf => exact False.elim hlt
    | finite val2 =>
      have hlt2 : LT.lt val val2 := hlt
      obtain ⟨y, hy1, hy2⟩ := exists_between hlt2
      exact ⟨fun _ => y, hy1, hy2⟩
    | posInf =>
      obtain ⟨y, hym⟩ := exists_gt val
      exact ⟨fun _ => y, hym, trivial⟩
  | posInf => exact False.elim hlt

end Monotonicity_Theorem


theorem discBadMmem {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 8 (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1))) :=
  M.inter_mem (M.reindex_mem dIx f.domain_mem)
    (M.inter_mem (M.reindex_mem dGy f.graph_mem)
      (M.inter_mem (M.reindex_mem dD1y M.lt_mem)
        (M.inter_mem (M.reindex_mem dYD2 M.lt_mem)
          (M.compl_mem (M.inter_mem (M.reindex_mem dE1q M.lt_mem)
            (M.reindex_mem dQe2 M.lt_mem))))))

-- No bad (y,q) above a fixed delta/epsilon context: peel (y, q).
theorem discGood6mem {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 6 (fun x6 : Power R 6 => ¬ ∃ t : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t)) :=
  M.compl_mem (M.existsLast_mem (n := 6) (m := 2) (discBadMmem M f))

-- Delta-pair around x inside a good context: peel (d1, d2).
theorem discBad4mem {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 4 (fun x4 : Power R 4 => ¬ ∃ t : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t2)))
        (Power.append x4 t)) :=
  M.compl_mem (M.existsLast_mem (n := 4) (m := 2)
    (M.inter_mem (M.reindex_mem dD1x6 M.lt_mem)
      (M.inter_mem (M.reindex_mem dXD26 M.lt_mem) (discGood6mem M f))))

-- Discontinuity locus at a point: peel (w0, e1, e2).
theorem discMem {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (fun p : Power R 1 => ∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
        (Power.append p t)) :=
  M.existsLast_mem (n := 1) (m := 3)
    (M.inter_mem (M.reindex_mem dGx4 f.graph_mem)
      (M.inter_mem (M.reindex_mem dE1w4 M.lt_mem)
        (M.inter_mem (M.reindex_mem dWe24 M.lt_mem) (discBad4mem M f))))

-- Bridge reverse: a discontinuity witness tuple yields non-continuity.
theorem discWitnessRev {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (p : Power R 1) (t : Power R 3)
    (hW : (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
      (Power.append p t)) :
    ¬ ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun) p := by
  obtain ⟨hGw, he1w, hwe2, hNo⟩ := hW
  have eG : (fun j : Fin (1 + 1) => (Power.append p t) (dGx4 j)) =
      Power.append (fun _ => Power.coord1 p) (fun _ => t ⟨0, by decide⟩) := by
    funext j
    fin_cases j <;> rfl
  rw [eG] at hGw
  have eE1 : ((fun j : Fin 2 => (Power.append p t) (dE1w4 j)) 0) = t ⟨1, by decide⟩ := by
    rfl
  have eW1 : ((fun j : Fin 2 => (Power.append p t) (dE1w4 j)) 1) = t ⟨0, by decide⟩ := by
    rfl
  have eW2 : ((fun j : Fin 2 => (Power.append p t) (dWe24 j)) 0) = t ⟨0, by decide⟩ := by
    rfl
  have eE2 : ((fun j : Fin 2 => (Power.append p t) (dWe24 j)) 1) = t ⟨2, by decide⟩ := by
    rfl
  rw [eE1, eW1] at he1w
  rw [eW2, eE2] at hwe2
  rintro ⟨hpI, hCont⟩
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, hAll⟩ :=
    hCont (t ⟨0, by decide⟩) hGw (t ⟨1, by decide⟩) (t ⟨2, by decide⟩) he1w hwe2
  apply hNo
  refine ⟨(fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂), ?_, ?_, ?_⟩
  · have f1 : ((fun j : Fin 2 => (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) (dD1x6 j)) 0) = δ₁ := by
      rfl
    have f2 : ((fun j : Fin 2 => (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) (dD1x6 j)) 1) =
        Power.coord1 p := by
      rfl
    rw [f1, f2]
    exact hδ₁
  · have f1 : ((fun j : Fin 2 => (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) (dXD26 j)) 0) =
        Power.coord1 p := by
      rfl
    have f2 : ((fun j : Fin 2 => (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) (dXD26 j)) 1) = δ₂ := by
      rfl
    rw [f1, f2]
    exact hδ₂
  · rintro ⟨t3, hQ⟩
    obtain ⟨hIx, hGyv, hdy1, hdy2, hnev⟩ := hQ
    have eGy : (fun j : Fin (1 + 1) => (Power.append (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) t3) (dGy j)) =
        Power.append (fun _ => t3 ⟨0, by decide⟩) (fun _ => t3 ⟨1, by decide⟩) := by
      funext j
      fin_cases j <;> rfl
    rw [eGy] at hGyv
    have hIy : I (fun _ : Fin 1 => t3 ⟨0, by decide⟩) := by
      have eL : Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => t3 ⟨0, by decide⟩)
          (fun _ : Fin 1 => t3 ⟨1, by decide⟩)) = (fun _ : Fin 1 => t3 ⟨0, by decide⟩) := by
        funext i
        simp [Power.left, Power.append, Fin.append_left]
      obtain ⟨hxI, heq⟩ := hGyv
      exact eL ▸ hxI
    have g1 : ((fun j : Fin 2 => (Power.append (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) t3) (dD1y j)) 0) = δ₁ := by
      rfl
    have g2 : ((fun j : Fin 2 => (Power.append (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) t3) (dD1y j)) 1) =
        t3 ⟨0, by decide⟩ := by
      rfl
    have g3 : ((fun j : Fin 2 => (Power.append (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) t3) (dYD2 j)) 0) =
        t3 ⟨0, by decide⟩ := by
      rfl
    have g4 : ((fun j : Fin 2 => (Power.append (Power.append (Power.append p t)
        (fun k : Fin 2 => if _ : k.val = 0 then δ₁ else δ₂)) t3) (dYD2 j)) 1) = δ₂ := by
      rfl
    have hdy1' : LT.lt δ₁ (t3 ⟨0, by decide⟩) := by
      rw [← g1, ← g2]
      exact hdy1
    have hdy2' : LT.lt (t3 ⟨0, by decide⟩) δ₂ := by
      rw [← g3, ← g4]
      exact hdy2
    have hnev' : ¬ (LT.lt (t ⟨1, by decide⟩) (t3 ⟨1, by decide⟩) ∧
        LT.lt (t3 ⟨1, by decide⟩) (t ⟨2, by decide⟩)) :=
      hnev
    exact hnev' (hAll _ _ hIy hGyv hdy1' hdy2')

theorem disc_finite_aux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    Set.Finite (fun p : Power R 1 => ∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
      (Power.append p t)) := by
  by_contra hne
  have hInf : Set.Infinite _ := hne
  have hDmem : M.S 1 (fun p : Power R 1 => ∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
      (Power.append p t)) :=
    discMem M f
  obtain ⟨c, d, hltAB, hsubAB⟩ :=
    Monotonicity_Theorem.infinite_definable_set_contains_interval2 M _ hDmem hInf
  obtain ⟨q₀, -⟩ := hInf.nonempty
  have hJne : (openInterval c d).Nonempty := nonemptyWinAux hltAB q₀
  obtain ⟨p, hp⟩ := hJne
  obtain ⟨u, v, huv, hsubUV⟩ := finiteSubwindowAux hp
  have hJ'D : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x →
      (∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
      (Power.append x t)) :=
    fun x hx => hsubAB (hsubUV x hx)
  have hJ'inf : Set.Infinite (openInterval (Endpoint.finite u) (Endpoint.finite v)) := by
    intro hfin
    have hfin' : Set.Finite (openInterval (Endpoint.finite u) (Endpoint.finite v)) := hfin
    set LC : List R := hfin'.toFinset.image Power.coord1 |>.toList with hLCdef
    have hLC : ∀ x : Power R 1, openInterval (Endpoint.finite u) (Endpoint.finite v) x →
        Power.coord1 x ∈ LC := by
      intro x hx
      rw [hLCdef]
      exact Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨x, hfin'.mem_toFinset.mpr hx, rfl⟩)
    exact intervalInfiniteAux LC u v huv hLC
  -- Witness points lie in I (graph part forces domain membership).
  have hJI : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x → I x := by
    intro x hx
    obtain ⟨t, hWt⟩ := hJ'D x hx
    obtain ⟨hGw, -, -, -⟩ := hWt
    have eG : (fun j : Fin (1 + 1) => (Power.append x t) (dGx4 j)) =
        Power.append (fun _ : Fin 1 => Power.coord1 x) (fun _ => t ⟨0, by decide⟩) := by
      funext j
      fin_cases j <;> rfl
    rw [eG] at hGw
    obtain ⟨hx0, heq0⟩ := hGw
    have eL : Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => Power.coord1 x)
        (fun _ : Fin 1 => t ⟨0, by decide⟩)) = (fun _ : Fin 1 => Power.coord1 x) := by
      funext i
      simp [Power.left, Power.append, Fin.append_left]
    rw [eL] at hx0
    exact (ptLam x).symm ▸ hx0
  obtain ⟨r, hr1, hr2⟩ := exists_between huv
  have hA'ne : ((openInterval (Endpoint.finite u) (Endpoint.finite v)) ∩ I).Nonempty :=
    ⟨(fun _ : Fin 1 => r), ⟨hr1, hr2⟩, hJI _ ⟨hr1, hr2⟩⟩
  obtain ⟨p₀, hp₀⟩ := hA'ne
  set A' : Set (Power R 1) :=
    (openInterval (Endpoint.finite u) (Endpoint.finite v)) ∩ I with hAdef
  have hA'mem : M.S 1 A' :=
    M.inter_mem ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)) f.domain_mem
  have hAsub : A'.Subset I := fun x hx => hx.right
  have hAJ' : (openInterval (Endpoint.finite u) (Endpoint.finite v)).Subset A' :=
    fun x hx => Set.mem_inter hx (hJI x hx)
  have hI'A : Set.Infinite A' := by
    intro hfin
    apply hJ'inf
    have hfin' : Set.Finite A' := hfin
    exact hfin'.subset hAJ'
  obtain ⟨f', hagree⟩ := restrictDefinable f A' hA'mem hAsub
  obtain ⟨e1, e2, hlt12, hsub12, hconstOrInj⟩ :=
    Monotonicity_Theorem.lemma_one M f' hI'A
  have hWne : (openInterval e1 e2).Nonempty := nonemptyWinAux hlt12 p₀
  obtain ⟨w₀, hw₀⟩ := hWne
  have hWD : ∀ x, openInterval e1 e2 x →
      (∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
      (Power.append x t)) := by
    intro x hx
    have hAx : A' x := hsub12 hx
    rw [hAdef] at hAx
    exact hJ'D x hAx.left
  have hWI : ∀ x, openInterval e1 e2 x → I x := by
    intro x hx
    exact hAsub (hsub12 hx)
  rcases hconstOrInj with hconst | hinj
  · -- Constant on W: shrink to finite window, continuous, against the bridge.
    obtain ⟨s, t, hs, ht, hsubST⟩ := shrinkWindowAux hw₀
    have hsubST_I : ∀ x, openInterval (Endpoint.finite s) (Endpoint.finite t) x → I x := by
      intro x hx
      exact hWI x (hsubST x hx)
    have hconstST : ∀ x (hxI : I x), openInterval (Endpoint.finite s) (Endpoint.finite t) x →
        ∀ y (hyI : I y), openInterval (Endpoint.finite s) (Endpoint.finite t) y →
        (f.toFun ⟨x, hxI⟩).1 = (f.toFun ⟨y, hyI⟩).1 := by
      intro x hxI hJx y hyI hJy
      have hxA : A' x := hsub12 (hsubST x hJx)
      have hyA : A' y := hsub12 (hsubST y hJy)
      have hval : f'.toFun ⟨x, hxA⟩ = f'.toFun ⟨y, hyA⟩ :=
        hconst x hxA (hsubST x hJx) y hyA (hsubST y hJy)
      have hagx : f'.toFun ⟨x, hxA⟩ = f.toFun ⟨x, hxI⟩ := by
        have e := hagree x hxA
        have esub : (⟨x, hAsub hxA⟩ : {x : Power R 1 // I x}) = ⟨x, hxI⟩ :=
          Subtype.ext rfl
        rw [esub] at e
        exact e
      have hagy : f'.toFun ⟨y, hyA⟩ = f.toFun ⟨y, hyI⟩ := by
        have e := hagree y hyA
        have esub : (⟨y, hAsub hyA⟩ : {x : Power R 1 // I x}) = ⟨y, hyI⟩ :=
          Subtype.ext rfl
        rw [esub] at e
        exact e
      rw [← hagx, ← hagy]
      exact congrArg Subtype.val hval
    have hcont := Monotonicity_Theorem.const_cont_of_const M f s t hsubST_I hconstST
    have hCw₀ := hcont ⟨hs, ht⟩
    obtain ⟨t, hWt⟩ := hWD w₀ hw₀
    exact discWitnessRev M f w₀ t hWt hCw₀
  · -- Injective on W: shrink to finite window, Lemma 2, Lemma 3 inside.
    obtain ⟨u₀, v₀, hu₀, hv₀, hsubW₀⟩ := shrinkWindowAux hw₀
    have huv₀ : LT.lt u₀ v₀ := lt_trans hu₀ hv₀
    set J₁ : Set (Power R 1) := openInterval (Endpoint.finite u₀) (Endpoint.finite v₀) with hJ₁def
    have hJ₁W : ∀ x, J₁ x → openInterval e1 e2 x := fun x hx => hsubW₀ x hx
    have hJ₁A' : ∀ x, J₁ x → A' x := by
      intro x hx
      exact hsub12 (hJ₁W x hx)
    set A₁ : Set (Power R 1) := (J₁ ∩ A') with hA₁def
    have hA₁mem : M.S 1 A₁ :=
      M.inter_mem ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)) hA'mem
    have hA₁sub : A₁.Subset A' := fun x hx => hx.right
    have hA₁J : ∀ x, A₁ x → J₁ x := fun x hx => hx.left
    have hI₁ : Set.Infinite A₁ := by
      intro hfin
      have hfin' : Set.Finite A₁ := hfin
      set LC : List R := hfin'.toFinset.image Power.coord1 |>.toList with hLCdef
      have hLC : ∀ x : Power R 1, J₁ x → Power.coord1 x ∈ LC := by
        intro x hx
        rw [hLCdef]
        exact Finset.mem_toList.mpr
          (Finset.mem_image.mpr ⟨x, hfin'.mem_toFinset.mpr ⟨hx, hJ₁A' x hx⟩, rfl⟩)
      exact intervalInfiniteAux LC u₀ v₀ huv₀ hLC
    obtain ⟨f₁, hagree₁⟩ := restrictDefinable f' A₁ hA₁mem hA₁sub
    have hinj₁ : ∀ x y (hx : A₁ x) (hy : A₁ y),
        f₁.toFun (Subtype.mk x hx) = f₁.toFun (Subtype.mk y hy) → x = y := by
      intro x y hx hy hval
      have hval' : f'.toFun (Subtype.mk x (hA₁sub hx)) =
          f'.toFun (Subtype.mk y (hA₁sub hy)) := by
        have e1 := hagree₁ x hx
        have e2 := hagree₁ y hy
        rw [e1, e2] at hval
        exact hval
      have hxW : openInterval e1 e2 x := hJ₁W x (hA₁J x hx)
      have hyW : openInterval e1 e2 y := hJ₁W y (hA₁J y hy)
      have hxA : A' x := hA₁sub hx
      have hyA : A' y := hA₁sub hy
      exact hinj _ hxA hxW _ hyA hyW hval'
    obtain ⟨a2, b2, hlt2, hsub2, hor⟩ :=
      Monotonicity_Theorem.lemma_two M f₁ hI₁ hinj₁
    have hW'ne : (openInterval a2 b2).Nonempty := nonemptyWinAux hlt2 p₀
    obtain ⟨w₁, hw₁⟩ := hW'ne
    have hW'D : ∀ x, openInterval a2 b2 x →
        (∃ t : Power R 3,
        (fun x4 : Power R 4 =>
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
        LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
        (¬ ∃ t2 : Power R 2,
        (fun x6 : Power R 6 =>
        LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
        (¬ ∃ t3 : Power R 2,
        (fun q : Power R 8 =>
        I (fun i : Fin 1 => q (dIx i)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (dGy j)) ∧
        LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
        ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
          (Power.append x6 t3)))
          (Power.append x4 t2)))
        (Power.append x t)) := by
      intro x hx
      have hA₁x : A₁ x := hsub2 x hx
      have hAx : A' x := hA₁sub hA₁x
      rw [hAdef] at hAx
      have hUx : openInterval (Endpoint.finite u) (Endpoint.finite v) x := hAx.left
      exact hJ'D x hUx
    have hmonof : (∀ x (hxI : I x), openInterval a2 b2 x →
        ∀ y (hyI : I y), openInterval a2 b2 y → Lt1 x y →
        Lt1 (f.toFun ⟨x, hxI⟩).1 (f.toFun ⟨y, hyI⟩).1) ∨
        (∀ x (hxI : I x), openInterval a2 b2 x →
        ∀ y (hyI : I y), openInterval a2 b2 y → Lt1 x y →
        Lt1 (f.toFun ⟨y, hyI⟩).1 (f.toFun ⟨x, hxI⟩).1) := by
      rcases hor with hinc | hdec
      · left
        intro x hxI hJx y hyI hJy hlt
        have hxA : A₁ x := hsub2 x hJx
        have hyA : A₁ y := hsub2 y hJy
        have hval : Lt1 (f₁.toFun ⟨x, hxA⟩).1 (f₁.toFun ⟨y, hyA⟩).1 :=
          hinc x hxA y hyA hJx hJy hlt
        have eX : f₁.toFun ⟨x, hxA⟩ = f.toFun ⟨x, hxI⟩ := by
          have e1 := hagree₁ x hxA
          have e2 := hagree x (hA₁sub hxA)
          have esub : (⟨x, hAsub (hA₁sub hxA)⟩ : {x : Power R 1 // I x}) = ⟨x, hxI⟩ :=
            Subtype.ext rfl
          rw [esub] at e2
          exact Eq.trans e1 e2
        have eY : f₁.toFun ⟨y, hyA⟩ = f.toFun ⟨y, hyI⟩ := by
          have e1 := hagree₁ y hyA
          have e2 := hagree y (hA₁sub hyA)
          have esub : (⟨y, hAsub (hA₁sub hyA)⟩ : {x : Power R 1 // I x}) = ⟨y, hyI⟩ :=
            Subtype.ext rfl
          rw [esub] at e2
          exact Eq.trans e1 e2
        rw [← eX, ← eY]
        exact hval
      · right
        intro x hxI hJx y hyI hJy hlt
        have hxA : A₁ x := hsub2 x hJx
        have hyA : A₁ y := hsub2 y hJy
        have hval : Lt1 (f₁.toFun ⟨y, hyA⟩).1 (f₁.toFun ⟨x, hxA⟩).1 :=
          hdec x hxA y hyA hJx hJy hlt
        have eX : f₁.toFun ⟨x, hxA⟩ = f.toFun ⟨x, hxI⟩ := by
          have e1 := hagree₁ x hxA
          have e2 := hagree x (hA₁sub hxA)
          have esub : (⟨x, hAsub (hA₁sub hxA)⟩ : {x : Power R 1 // I x}) = ⟨x, hxI⟩ :=
            Subtype.ext rfl
          rw [esub] at e2
          exact Eq.trans e1 e2
        have eY : f₁.toFun ⟨y, hyA⟩ = f.toFun ⟨y, hyI⟩ := by
          have e1 := hagree₁ y hyA
          have e2 := hagree y (hA₁sub hyA)
          have esub : (⟨y, hAsub (hA₁sub hyA)⟩ : {x : Power R 1 // I x}) = ⟨y, hyI⟩ :=
            Subtype.ext rfl
          rw [esub] at e2
          exact Eq.trans e1 e2
        rw [← eX, ← eY]
        exact hval
    set A₂ : Set (Power R 1) := (openInterval a2 b2) ∩ I with hA₂def
    have hA₂mem : M.S 1 A₂ :=
      M.inter_mem ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)) f.domain_mem
    have hA₂sub : A₂.Subset I := fun x hx => hx.right
    have hA₂W' : ∀ x, A₂ x → openInterval a2 b2 x := fun x hx => hx.left
    have hI₂ : Set.Infinite A₂ := by
      intro hfin
      have hfin' : Set.Finite A₂ := hfin
      obtain ⟨s, t, hs, ht, hsubST⟩ := shrinkWindowAux hw₁
      have hSTne : ∀ x : Power R 1, openInterval (Endpoint.finite s) (Endpoint.finite t) x →
          A₂ x := by
        intro x hx
        have hW'x : openInterval a2 b2 x := hsubST x hx
        have hA₁x : A₁ x := hsub2 x hW'x
        have hIx : I x := hAsub (hA₁sub hA₁x)
        show openInterval a2 b2 x ∧ I x
        exact ⟨hW'x, hIx⟩
      set LC : List R := hfin'.toFinset.image Power.coord1 |>.toList with hLCdef
      have hLC : ∀ x : Power R 1, openInterval (Endpoint.finite s) (Endpoint.finite t) x →
          Power.coord1 x ∈ LC := by
        intro x hx
        rw [hLCdef]
        exact Finset.mem_toList.mpr
          (Finset.mem_image.mpr ⟨x, hfin'.mem_toFinset.mpr (hSTne x hx), rfl⟩)
      have hst : LT.lt s t := lt_trans hs ht
      exact intervalInfiniteAux LC s t hst hLC
    obtain ⟨f₂, hagree₂⟩ := restrictDefinable f A₂ hA₂mem hA₂sub
    have hmono₂ : StrictlyMonotoneOn A₂ B f₂.toFun := by
      rcases hmonof with hinc | hdec
      · left
        intro x y hx hy hlt
        have hJx : openInterval a2 b2 x := hA₂W' x hx
        have hJy : openInterval a2 b2 y := hA₂W' y hy
        have hxI : I x := hA₂sub hx
        have hyI : I y := hA₂sub hy
        have hval : Lt1 (f.toFun ⟨x, hxI⟩).1 (f.toFun ⟨y, hyI⟩).1 :=
          hinc x hxI hJx y hyI hJy hlt
        have eX : f₂.toFun ⟨x, hx⟩ = f.toFun ⟨x, hxI⟩ := by
          have e := hagree₂ x hx
          have esub : (⟨x, hA₂sub hx⟩ : {x : Power R 1 // I x}) = ⟨x, hxI⟩ :=
            Subtype.ext rfl
          rw [esub] at e
          exact e
        have eY : f₂.toFun ⟨y, hy⟩ = f.toFun ⟨y, hyI⟩ := by
          have e := hagree₂ y hy
          have esub : (⟨y, hA₂sub hy⟩ : {x : Power R 1 // I x}) = ⟨y, hyI⟩ :=
            Subtype.ext rfl
          rw [esub] at e
          exact e
        rw [eX, eY]
        exact hval
      · right
        intro x y hx hy hlt
        have hJx : openInterval a2 b2 x := hA₂W' x hx
        have hJy : openInterval a2 b2 y := hA₂W' y hy
        have hxI : I x := hA₂sub hx
        have hyI : I y := hA₂sub hy
        have hval : Lt1 (f.toFun ⟨y, hyI⟩).1 (f.toFun ⟨x, hxI⟩).1 :=
          hdec x hxI hJx y hyI hJy hlt
        have eX : f₂.toFun ⟨x, hx⟩ = f.toFun ⟨x, hxI⟩ := by
          have e := hagree₂ x hx
          have esub : (⟨x, hA₂sub hx⟩ : {x : Power R 1 // I x}) = ⟨x, hxI⟩ :=
            Subtype.ext rfl
          rw [esub] at e
          exact e
        have eY : f₂.toFun ⟨y, hy⟩ = f.toFun ⟨y, hyI⟩ := by
          have e := hagree₂ y hy
          have esub : (⟨y, hA₂sub hy⟩ : {x : Power R 1 // I x}) = ⟨y, hyI⟩ :=
            Subtype.ext rfl
          rw [esub] at e
          exact e
        rw [eX, eY]
        exact hval
    obtain ⟨a3, b3, hlt3, hsub3A, hsub3C⟩ :=
      Monotonicity_Theorem.lemma_three2 M f₂ hmono₂ hI₂
    have hW3ne : (openInterval a3 b3).Nonempty := nonemptyWinAux hlt3 p₀
    obtain ⟨z, hz⟩ := hW3ne
    have hDz : (∃ t : Power R 3,
        (fun x4 : Power R 4 =>
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
        LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
        (¬ ∃ t2 : Power R 2,
        (fun x6 : Power R 6 =>
        LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
        (¬ ∃ t3 : Power R 2,
        (fun q : Power R 8 =>
        I (fun i : Fin 1 => q (dIx i)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (dGy j)) ∧
        LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
        ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
          (Power.append x6 t3)))
          (Power.append x4 t2)))
        (Power.append z t)) := by
      have hA₂z : A₂ z := hsub3A hz
      have hW'z : openInterval a2 b2 z := hA₂W' z hA₂z
      have hA₁z : A₁ z := hsub2 z hW'z
      have hAz : A' z := hA₁sub hA₁z
      rw [hAdef] at hAz
      exact hJ'D z hAz.left
    have hCz : ContinuousPoints I
        (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun) z := by
      have hA₂z : A₂ z := hsub3A hz
      obtain ⟨s, t, hs, ht, hsubST⟩ := shrinkWindowAux hz
      have hC₂z := hsub3C hz
      obtain ⟨hzA₂, hP₂⟩ := hC₂z
      have hzx : z = (fun _ : Fin 1 => Power.coord1 z) := ptLam z
      have hIx : I z := hA₂sub hA₂z
      refine ⟨hIx, ?_⟩
      intro w₀ hG ε₁ ε₂ he₁ he₂
      have hG₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := A₂) (B := B) f₂.toFun
          (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z) (fun _ => w₀)) := by
        obtain ⟨hx0, heq0⟩ := hG
        have eL : Power.left (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
            (fun _ => w₀)) = (fun _ => Power.coord1 z) := by
          funext i
          simp [Power.left, Power.append, Fin.append_left]
        have eR : Power.right (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
            (fun _ => w₀)) = (fun _ => w₀) := by
          funext j
          fin_cases j
          rfl
        have hxA₂ : A₂ (Power.left (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
            (fun _ => w₀))) := by
          rw [eL]
          rw [← hzx]
          exact hA₂z
        refine ⟨hxA₂, ?_⟩
        have hval : (f₂.toFun ⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
            (fun _ => w₀)), hxA₂⟩).1 = (f.toFun ⟨z, hIx⟩).1 := by
          have e := hagree₂ _ hxA₂
          have esub : (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
              (fun _ => w₀)), hA₂sub hxA₂⟩ : {x : Power R 1 // I x}) =
              ⟨z, hIx⟩ := Subtype.ext (eL.trans hzx.symm)
          rw [esub] at e
          exact congrArg Subtype.val e
        have hval0 : Power.right (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
            (fun _ => w₀)) = (f.toFun ⟨z, hIx⟩).1 := by
          have hsubz : (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
              (fun _ => w₀)), hx0⟩ : {x : Power R 1 // I x}) =
              (⟨z, hIx⟩ : {x : Power R 1 // I x}) :=
            Subtype.ext (eL.trans hzx.symm)
          calc Power.right (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
              (fun _ => w₀))
              = (f.toFun (⟨Power.left (Power.append (n := 1) (m := 1)
                  (fun _ => Power.coord1 z) (fun _ => w₀)), hx0⟩ :
                {x : Power R 1 // I x})).1 := heq0
            _ = (f.toFun ⟨z, hIx⟩).1 := by rw [hsubz]
        calc Power.right (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
            (fun _ => w₀))
            = (f.toFun ⟨z, hIx⟩).1 := hval0
          _ = (f₂.toFun ⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 z)
              (fun _ => w₀)), hxA₂⟩).1 := hval.symm
      obtain ⟨δ₁, δ₂, hδ₁, hδ₂, hAll₂⟩ := hP₂ w₀ hG₂ ε₁ ε₂ he₁ he₂
      have hxs : LT.lt s (Power.coord1 z) := hs
      have hxt : LT.lt (Power.coord1 z) t := ht
      have hδ₁x : LT.lt δ₁ (Power.coord1 z) := hδ₁
      have hxδ₂ : LT.lt (Power.coord1 z) δ₂ := hδ₂
      obtain ⟨d₁, hd₁A, hd₁BC⟩ : ∃ d₁ : R, (LT.lt δ₁ d₁ ∨ δ₁ = d₁) ∧
          (LT.lt s d₁ ∨ s = d₁) ∧ LT.lt d₁ (Power.coord1 z) := by
        rcases lt_trichotomy δ₁ s with h | h | h
        · obtain ⟨m, hm1, hm2⟩ := exists_between hxs
          exact ⟨m, Or.inl (lt_trans h hm1), Or.inl hm1, hm2⟩
        · subst h
          obtain ⟨m, hm1, hm2⟩ := exists_between hxs
          exact ⟨m, Or.inl hm1, Or.inl hm1, hm2⟩
        · obtain ⟨m, hm1, hm2⟩ := exists_between hδ₁x
          exact ⟨m, Or.inl hm1, Or.inl (lt_trans h hm1), hm2⟩
      obtain ⟨d₂, hd₂A, hd₂BC⟩ : ∃ d₂ : R, (LT.lt d₂ δ₂ ∨ d₂ = δ₂) ∧
          (LT.lt d₂ t ∨ d₂ = t) ∧ LT.lt (Power.coord1 z) d₂ := by
        rcases lt_trichotomy δ₂ t with h | h | h
        · obtain ⟨m, hm1, hm2⟩ := exists_between hxδ₂
          exact ⟨m, Or.inl hm2, Or.inl (lt_trans hm2 h), hm1⟩
        · subst h
          obtain ⟨m, hm1, hm2⟩ := exists_between hxδ₂
          exact ⟨m, Or.inl hm2, Or.inl hm2, hm1⟩
        · obtain ⟨m, hm1, hm2⟩ := exists_between hxt
          exact ⟨m, Or.inl (lt_trans hm2 h), Or.inl hm2, hm1⟩
      obtain ⟨hd₁B, hd₁x⟩ := hd₁BC
      obtain ⟨hd₂B, hd₂x⟩ := hd₂BC
      refine ⟨d₁, d₂, hd₁x, hd₂x, ?_⟩
      intro y v hyI hGyv hdy1 hdy2
      have hδy1 : LT.lt δ₁ y := by
        rcases hd₁A with h | h
        · exact lt_trans h hdy1
        · rw [← h] at hdy1
          exact hdy1
      have hδy2 : LT.lt y δ₂ := by
        rcases hd₂A with h | h
        · exact lt_trans hdy2 h
        · rw [h] at hdy2
          exact hdy2
      have hyst : openInterval (Endpoint.finite s) (Endpoint.finite t) (fun _ => y) := by
        constructor
        · rcases hd₁B with h | h
          · exact lt_trans h hdy1
          · rw [← h] at hdy1; exact hdy1
        · rcases hd₂B with h | h
          · exact lt_trans hdy2 h
          · rw [h] at hdy2; exact hdy2
      have hyW' : openInterval a2 b2 (fun _ => y) := by
        have h3 : openInterval a3 b3 (fun _ => y) := hsubST _ hyst
        have hA₂y : A₂ (fun _ => y) := hsub3A h3
        exact hA₂W' _ hA₂y
      have eLy : Power.left (Power.append (n := 1) (m := 1) (fun _ => y)
          (fun _ => v)) = (fun _ => y) := by
        funext i
        simp [Power.left, Power.append, Fin.append_left]
      have eRy : Power.right (Power.append (n := 1) (m := 1) (fun _ => y)
          (fun _ => v)) = (fun _ => v) := by
        funext j
        fin_cases j
        rfl
      have hyA₂ : A₂ (Power.left (Power.append (n := 1) (m := 1) (fun _ => y)
          (fun _ => v))) := by
        rw [eLy]
        show openInterval a2 b2 (fun _ => y) ∧ I (fun _ => y)
        exact ⟨hyW', hyI⟩
      have hGyv₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := A₂) (B := B) f₂.toFun
          (Power.append (n := 1) (m := 1) (fun _ => y) (fun _ => v)) := by
        obtain ⟨hy0, heq⟩ := hGyv
        refine ⟨hyA₂, ?_⟩
        have hval : (f₂.toFun ⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => y)
            (fun _ => v)), hyA₂⟩).1 = (f.toFun ⟨fun _ => y, hyI⟩).1 := by
          have e := hagree₂ _ hyA₂
          have esub : (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => y)
              (fun _ => v)), hA₂sub hyA₂⟩ : {x : Power R 1 // I x}) =
              ⟨fun _ => y, hyI⟩ := Subtype.ext eLy
          rw [esub] at e
          exact congrArg Subtype.val e
        have hval0 : Power.right (Power.append (n := 1) (m := 1) (fun _ => y)
            (fun _ => v)) = (f.toFun ⟨fun _ => y, hyI⟩).1 := by
          have hsuby : (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => y)
              (fun _ => v)), hy0⟩ : {x : Power R 1 // I x}) =
              (⟨fun _ => y, hyI⟩ : {x : Power R 1 // I x}) := Subtype.ext eLy
          calc Power.right (Power.append (n := 1) (m := 1) (fun _ => y)
              (fun _ => v))
              = (f.toFun (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => y)
                  (fun _ => v)), hy0⟩ : {x : Power R 1 // I x})).1 := heq
            _ = (f.toFun ⟨fun _ => y, hyI⟩).1 := by rw [hsuby]
        calc Power.right (Power.append (n := 1) (m := 1) (fun _ => y)
            (fun _ => v))
            = (f.toFun ⟨fun _ => y, hyI⟩).1 := hval0
          _ = (f₂.toFun ⟨Power.left (Power.append (n := 1) (m := 1) (fun _ => y)
              (fun _ => v)), hyA₂⟩).1 := hval.symm
      have hyA₂lam : A₂ (fun _ => y) := by
        rw [← eLy]
        exact hyA₂
      exact hAll₂ y v hyA₂lam hGyv₂ hδy1 hδy2
    obtain ⟨t, hWt⟩ := hDz
    exact discWitnessRev M f z t hWt hCz


open Monotonicity_Theorem


open Monotonicity_Theorem

-- Every finite union has a coordinate list covering all its point-coords and
-- finite interval-endpoints, over which pieces strictly between consecutive
-- listed points are atomic (disjoint from S or contained in S).
theorem atomicExists {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (S : Set (Power R 1)) (hFU : FiniteUnionOfPointsAndIntervals S) :
    ∃ L : List R, ∀ (E : List R), (∀ c ∈ L, c ∈ E) →
    ∀ (l r : R), (∀ e ∈ E, ¬ (LT.lt l e ∧ LT.lt e r)) →
    ((∀ x, openInterval (Endpoint.finite l) (Endpoint.finite r) x → ¬ S x) ∨
    (∀ x, openInterval (Endpoint.finite l) (Endpoint.finite r) x → S x)) := by
  refine FiniteUnionOfPointsAndIntervals.rec
    (motive := fun (T : Set (Power R 1)) (_ : FiniteUnionOfPointsAndIntervals T) =>
      ∃ L : List R, ∀ (E : List R), (∀ c ∈ L, c ∈ E) →
      ∀ (l r : R), (∀ e ∈ E, ¬ (LT.lt l e ∧ LT.lt e r)) →
      ((∀ x, openInterval (Endpoint.finite l) (Endpoint.finite r) x → ¬ T x) ∨
      (∀ x, openInterval (Endpoint.finite l) (Endpoint.finite r) x → T x)))
    ?_ ?_ ?_ ?_ hFU
  · -- empty
    refine ⟨[], fun E _ l r _ => ?_⟩
    left
    intro x hx hSx
    exact hSx
  · -- point
    intro c
    refine ⟨[c], fun E hE l r hconsec => ?_⟩
    left
    intro x hx hSx
    have hcc : Power.coord1 x = c := hSx
    have hcE : c ∈ E := hE c (by simp)
    have hcr : LT.lt c r := hcc ▸ hx.right
    exact hconsec c hcE ⟨hcc ▸ hx.left, hcr⟩
  · -- interval
    intro a b
    refine ⟨(match a with | .finite v => [v] | _ => []) ++
      (match b with | .finite v => [v] | _ => []), fun E hE l r hconsec => ?_⟩
    by_cases hex : ∃ x, openInterval (Endpoint.finite l) (Endpoint.finite r) x ∧
      openInterval a b x
    · right
      intro y hy
      by_contra hyS
      obtain ⟨x₀, hx₀, hxS⟩ := hex
      cases a with
      | negInf =>
        cases b with
        | negInf =>
          have hcon : openInterval Endpoint.negInf Endpoint.negInf x₀ := hxS
          exact False.elim hcon.right
        | finite r0 =>
          have hrE : r0 ∈ E := hE r0 (by simp)
          rcases lt_trichotomy (Power.coord1 y) r0 with h | h | h
          · have hlt := h
            exact False.elim (hyS ⟨trivial, hlt⟩)
          · have heq := h
            exact hconsec r0 hrE ⟨by rw [← heq]; exact hy.left, by rw [← heq]; exact hy.right⟩
          · have hlt := h
            exact hconsec r0 hrE ⟨lt_trans hx₀.left hxS.right, lt_trans hlt hy.right⟩
        | posInf =>
          exact False.elim (hyS ⟨trivial, trivial⟩)
      | finite l0 =>
        cases b with
        | negInf =>
          have hcon : openInterval (Endpoint.finite l0) Endpoint.negInf x₀ := hxS
          exact False.elim hcon.right
        | finite r0 =>
          have hlE : l0 ∈ E := hE l0 (by simp)
          have hrE : r0 ∈ E := hE r0 (by simp)
          have hx0l : LT.lt l0 (Power.coord1 x₀) := hxS.left
          have hx0r : LT.lt (Power.coord1 x₀) r0 := hxS.right
          by_cases h1 : LT.lt l0 (Power.coord1 y)
          · by_cases h2 : LT.lt (Power.coord1 y) r0
            · exact False.elim (hyS ⟨h1, h2⟩)
            · have hyr : LT.lt r0 (Power.coord1 y) ∨ Power.coord1 y = r0 := by
                rcases lt_trichotomy (Power.coord1 y) r0 with h | h | h
                · exact False.elim (h2 h)
                · exact Or.inr h
                · exact Or.inl h
              rcases hyr with h | h
              · exact hconsec r0 hrE ⟨lt_trans hx₀.left hx0r, lt_trans h hy.right⟩
              · exact hconsec r0 hrE ⟨by rw [← h]; exact hy.left, by rw [← h]; exact hy.right⟩
          · have hyl : LT.lt (Power.coord1 y) l0 ∨ Power.coord1 y = l0 := by
              rcases lt_trichotomy (Power.coord1 y) l0 with h | h | h
              · exact Or.inl h
              · exact Or.inr h
              · exact False.elim (h1 h)
            rcases hyl with h | h
            · exact hconsec l0 hlE ⟨lt_trans hy.left h, lt_trans hx0l hx₀.right⟩
            · exact hconsec l0 hlE ⟨by rw [← h]; exact hy.left, by rw [← h]; exact hy.right⟩
        | posInf =>
          have hlE : l0 ∈ E := hE l0 (by simp)
          have hx0l : LT.lt l0 (Power.coord1 x₀) := hxS.left
          by_cases h1 : LT.lt l0 (Power.coord1 y)
          · exact False.elim (hyS ⟨h1, trivial⟩)
          · have hyl : LT.lt (Power.coord1 y) l0 ∨ Power.coord1 y = l0 := by
              rcases lt_trichotomy (Power.coord1 y) l0 with h | h | h
              · exact Or.inl h
              · exact Or.inr h
              · exact False.elim (h1 h)
            rcases hyl with h | h
            · exact hconsec l0 hlE ⟨lt_trans hy.left h, lt_trans hx0l hx₀.right⟩
            · have hlt2 : LT.lt l0 r := lt_trans hx0l hx₀.right
              exact hconsec l0 hlE ⟨by rw [← h]; exact hy.left, hlt2⟩
      | posInf =>
        have hcon : openInterval Endpoint.posInf b x₀ := hxS
        exact False.elim hcon.left
    · left
      intro x hx hSx
      exact False.elim (hex ⟨x, hx, hSx⟩)
  · -- union
    intro A B hFA hFB ihA ihB
    obtain ⟨LA, hLA⟩ := ihA
    obtain ⟨LB, hLB⟩ := ihB
    refine ⟨LA ++ LB, fun E hE l r hconsec => ?_⟩
    have hEA : ∀ c ∈ LA, c ∈ E := by
      intro c hc
      exact hE c (List.mem_append.mpr (Or.inl hc))
    have hEB : ∀ c ∈ LB, c ∈ E := by
      intro c hc
      exact hE c (List.mem_append.mpr (Or.inr hc))
    rcases hLA E hEA l r hconsec with hA | hA
    · rcases hLB E hEB l r hconsec with hB | hB
      · left
        intro x hx hSx
        rcases hSx with h | h
        · exact hA x hx h
        · exact hB x hx h
      · right
        intro x hx
        exact Or.inr (hB x hx)
    · rcases hLB E hEB l r hconsec with hB | hB
      · right
        intro x hx
        exact Or.inl (hA x hx)
      · right
        intro x hx
        exact Or.inl (hA x hx)

-- Sorted lists (strictly increasing) with insertion sort (classical decidability).
def SortedLT {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] : List R → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => LT.lt x y ∧ SortedLT (y :: ys)

noncomputable def insertSorted {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (x : R) : List R → List R
  | [] => [x]
  | y :: ys => if x = y then y :: ys
    else if LT.lt x y then x :: y :: ys
    else y :: insertSorted x ys

theorem insertSorted_self {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (x : R) (L : List R) : x ∈ insertSorted x L := by
  induction L with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x = y
    · rw [if_pos hxy]
      exact List.mem_cons.mpr (Or.inl hxy)
    · rw [if_neg hxy]
      by_cases hlt : LT.lt x y
      · rw [if_pos hlt]
        exact List.mem_cons.mpr (Or.inl rfl)
      · rw [if_neg hlt]
        exact List.mem_cons.mpr (Or.inr ih)

theorem insertSorted_mem {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (x : R) (L : List R) (c : R) :
    (c ∈ insertSorted x L) ↔ (c = x ∨ c ∈ L) := by
  induction L with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x = y
    · rw [if_pos hxy]
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact Or.inl (Eq.trans h hxy.symm)
        · exact Or.inr (List.mem_cons.mpr (Or.inr h))
      · intro h
        rcases h with h | h
        · rw [h]
          exact List.mem_cons.mpr (Or.inl hxy)
        · rcases List.mem_cons.mp h with h | h
          · rw [h]
            exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr h)
    · rw [if_neg hxy]
      by_cases hlt : LT.lt x y
      · rw [if_pos hlt]
        constructor
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h | h
            · exact Or.inr (List.mem_cons.mpr (Or.inl h))
            · exact Or.inr (List.mem_cons.mpr (Or.inr h))
        · intro h
          rcases h with h | h
          · rw [h]
            exact List.mem_cons.mpr (Or.inl rfl)
          · rcases List.mem_cons.mp h with h | h
            · rw [h]
              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
            · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
      · rw [if_neg hlt]
        constructor
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · have := ih.mp h
            rcases this with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons.mpr (Or.inr h))
        · intro h
          rcases h with h | h
          · rw [h]
            exact List.mem_cons.mpr (Or.inr (insertSorted_self x ys))
          · rcases List.mem_cons.mp h with h | h
            · rw [h]
              exact List.mem_cons.mpr (Or.inl rfl)
            · have hmem : c ∈ insertSorted x ys := ih.mpr (Or.inr h)
              exact List.mem_cons.mpr (Or.inr hmem)

theorem sortedTailAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (y : R) (ys : List R) (h : SortedLT (y :: ys)) : SortedLT ys := by
  cases ys with
  | nil => exact True.intro
  | cons z zs => exact h.right

-- Every later element exceeds the head.
theorem sortedMemGT {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a : R) (L : List R) (hS : SortedLT (a :: L)) (z : R) (hz : z ∈ L) :
    LT.lt a z := by
  induction L with
  | nil => simp at hz
  | cons b bs ih =>
    rcases List.mem_cons.mp hz with h | h
    · rw [h]
      exact hS.left
    · have habs : SortedLT (a :: bs) := by
        cases bs with
        | nil => exact True.intro
        | cons c cs => exact ⟨lt_trans hS.left hS.right.left, hS.right.right⟩
      exact ih habs h

-- Inserting above y preserves y-least sortedness.
theorem insertAboveAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (x y : R) (hyx : LT.lt y x) (ys : List R) (hys : SortedLT ys)
    (hy : ∀ z ∈ ys, LT.lt y z) : SortedLT (y :: insertSorted x ys) := by
  revert y hyx hy
  induction ys with
  | nil =>
    intro y hyx hy
    simp only [insertSorted]
    exact ⟨hyx, True.intro⟩
  | cons z zs ih =>
    intro y hyx hy
    simp only [insertSorted]
    have hzs : SortedLT zs := sortedTailAux z zs hys
    have hyz : LT.lt y z := hy z (List.mem_cons.mpr (Or.inl rfl))
    have hyzs : ∀ w ∈ zs, LT.lt y w := by
      intro w hw
      exact hy w (List.mem_cons.mpr (Or.inr hw))
    by_cases hxz : x = z
    · rw [if_pos hxz]
      exact ⟨hyz, hys⟩
    · rw [if_neg hxz]
      by_cases hxzlt : LT.lt x z
      · rw [if_pos hxzlt]
        exact ⟨hyx, hxzlt, hys⟩
      · rw [if_neg hxzlt]
        have hzx : LT.lt z x := by
          rcases lt_trichotomy z x with h | h | h
          · exact h
          · exact False.elim (hxz h.symm)
          · exact False.elim (hxzlt h)
        have hzxs : ∀ w ∈ zs, LT.lt z w := by
          intro w hw
          exact sortedMemGT z zs hys w hw
        have hrec := ih hzs z hzx hzxs
        exact ⟨hyz, hrec⟩

noncomputable def sortList {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] : List R → List R
  | [] => []
  | x :: xs => insertSorted x (sortList xs)

theorem insertSorted_sorted {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (x : R) (L : List R) (hL : SortedLT L) : SortedLT (insertSorted x L) := by
  induction L with
  | nil => exact True.intro
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x = y
    · rw [if_pos hxy]
      exact hL
    · rw [if_neg hxy]
      by_cases hlt : LT.lt x y
      · rw [if_pos hlt]
        exact ⟨hlt, hL⟩
      · rw [if_neg hlt]
        have hyx : LT.lt y x := by
          rcases lt_trichotomy y x with h | h | h
          · exact h
          · exact False.elim (hxy h.symm)
          · exact False.elim (hlt h)
        have hys : SortedLT ys := sortedTailAux y ys hL
        have hy : ∀ z ∈ ys, LT.lt y z := by
          intro z hz
          exact sortedMemGT y ys hL z hz
        exact insertAboveAux x y hyx ys hys hy

theorem sortList_sorted {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (L : List R) : SortedLT (sortList L) := by
  induction L with
  | nil => exact True.intro
  | cons x xs ih => exact insertSorted_sorted x (sortList xs) ih

theorem sortList_mem {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (L : List R) (c : R) : (c ∈ sortList L) ↔ (c ∈ L) := by
  induction L with
  | nil => simp [sortList]
  | cons x xs ih =>
    simp only [sortList]
    constructor
    · intro h
      have := (insertSorted_mem x (sortList xs) c).mp h
      rcases this with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · have := ih.mp h
        exact List.mem_cons.mpr (Or.inr this)
    · intro h
      rcases List.mem_cons.mp h with h | h
      · rw [h]
        exact (insertSorted_mem x (sortList xs) x).mpr (Or.inl rfl)
      · have := ih.mpr h
        exact (insertSorted_mem x (sortList xs) c).mpr (Or.inr this)

-- Adjacent elements of a sorted list are strictly ordered.
theorem sortedStepAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (L : List R) (hS : SortedLT L) (i : Nat) (hi : i + 1 < L.length) :
    LT.lt (L.get ⟨i, by omega⟩) (L.get ⟨i + 1, by omega⟩) := by
  revert i hi
  induction L with
  | nil =>
    intro i hi
    simp only [List.length] at hi
    have : False := by omega
    exact False.elim this
  | cons a as ih =>
    intro i hi
    cases as with
    | nil =>
      simp only [List.length] at hi
      have : False := by omega
      exact False.elim this
    | cons b bs =>
      match i with
      | 0 => exact hS.left
      | j + 1 =>
        have htail : SortedLT (b :: bs) := hS.right
        have hlen : (a :: b :: bs).length = (b :: bs).length + 1 := rfl
        have hj : j + 1 < (b :: bs).length := by omega
        exact ih htail j hj

-- Chained order along a sorted list.
theorem sortedChainAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (L : List R) (hS : SortedLT L) (i d : Nat) (hi : i + d + 1 < L.length) :
    LT.lt (L.get ⟨i, by omega⟩) (L.get ⟨i + d + 1, by omega⟩) := by
  induction d with
  | zero => exact sortedStepAux L hS i hi
  | succ n ihn =>
    have h1 : i + n + 1 < L.length := by omega
    have h2 : i + n + 1 + 1 < L.length := by omega
    have g1 : LT.lt (L.get ⟨i, by omega⟩) (L.get ⟨i + n + 1, by omega⟩) := ihn h1
    have g2 : LT.lt (L.get ⟨i + n + 1, by omega⟩) (L.get ⟨i + (n + 1) + 1, by omega⟩) :=
      sortedStepAux L hS (i + n + 1) h2
    exact lt_trans g1 g2

-- Lambda-form equality at arity-8 positions is definable.
theorem lambdaEqDefinable8 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) :
    M.S 8 (fun t : Power R 8 => ((fun _ : Fin 1 => t (⟨6, by decide⟩ : Fin 8)) =
      (fun _ : Fin 1 => t (⟨7, by decide⟩ : Fin 8)))) := by
  have heq : (fun t : Power R 8 => ((fun _ : Fin 1 => t (⟨6, by decide⟩ : Fin 8)) =
      (fun _ : Fin 1 => t (⟨7, by decide⟩ : Fin 8)))) =
      (fun t : Power R 8 => t (⟨6, by decide⟩ : Fin 8) = t (⟨7, by decide⟩ : Fin 8)) := by
    funext t
    apply propext
    constructor
    · intro h
      exact congrFun h ⟨0, by decide⟩
    · intro h
      funext i
      exact h
  rw [heq]
  exact M.diagonal_mem (⟨6, by decide⟩ : Fin 8)
    (⟨7, by decide⟩ : Fin 8) (by decide)

-- Lambda-form non-equality at arity-8 positions is definable.
theorem lambdaNeqDefinable8 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) :
    M.S 8 (fun t : Power R 8 => ¬ ((fun _ : Fin 1 => t (⟨6, by decide⟩ : Fin 8)) =
      (fun _ : Fin 1 => t (⟨7, by decide⟩ : Fin 8)))) := by
  have heq : (fun t : Power R 8 => ¬ ((fun _ : Fin 1 => t (⟨6, by decide⟩ : Fin 8)) =
      (fun _ : Fin 1 => t (⟨7, by decide⟩ : Fin 8)))) =
      (fun t : Power R 8 => ¬ t (⟨6, by decide⟩ : Fin 8) = t (⟨7, by decide⟩ : Fin 8)) := by
    funext t
    apply propext
    constructor
    · intro h hcon
      apply h
      funext i
      exact hcon
    · intro h hcon
      apply h
      exact congrFun hcon ⟨0, by decide⟩
  rw [heq]
  exact M.compl_mem (M.diagonal_mem (⟨6, by decide⟩ : Fin 8)
    (⟨7, by decide⟩ : Fin 8) (by decide))

-- Index maps for rightward-const-prefix matrix.
-- Tuple layout (arity 8): 0:c, 1:lo, 2:hi, 3:x0, 4:p, 5:q, 6:wp, 7:wq.
def pxPtLo : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨4, by decide⟩
def pxPtHi : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨2, by decide⟩
def pxQtLo : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨5, by decide⟩
def pxQtHi : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨5, by decide⟩ else ⟨2, by decide⟩
def pxRX0p : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨3, by decide⟩ else ⟨4, by decide⟩
def pxRPc : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨0, by decide⟩
def pxRX0q : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨3, by decide⟩ else ⟨5, by decide⟩
def pxRQc : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨5, by decide⟩ else ⟨0, by decide⟩
def pxIp : Fin 1 → Fin 8 := fun _ => ⟨4, by decide⟩
def pxIq : Fin 1 → Fin 8 := fun _ => ⟨5, by decide⟩
def pxGp : Fin (1 + 1) → Fin 8 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨6, by decide⟩
def pxGq : Fin (1 + 1) → Fin 8 := fun j => if _ : j.val = 0 then ⟨5, by decide⟩ else ⟨7, by decide⟩
-- Window/param maps over (c, lo, hi, x0) : Fin 4.
def wqPcLo : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩
def wqPcHi : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
def wqX0C : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨3, by decide⟩ else ⟨0, by decide⟩
def wqPlo : Fin 1 → Fin 4 := fun _ => ⟨1, by decide⟩
def wqPhi : Fin 1 → Fin 4 := fun _ => ⟨2, by decide⟩
def wqPx0 : Fin 1 → Fin 4 := fun _ => ⟨3, by decide⟩
-- Flipped X0-window map (c < x0) for leftward prefixes.
def wqCX0 : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩
-- Leftward-range maps (range [c, x0]).
def pxCPc : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨4, by decide⟩
def pxPcX0 : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨3, by decide⟩
def pxCQc : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨5, by decide⟩
def pxQcX0 : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨5, by decide⟩ else ⟨3, by decide⟩
-- p<q and value-BAD maps.
def pxLTpq : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨4, by decide⟩ else ⟨5, by decide⟩
-- W-level violation maps: BADU = decreasing pair (wqc < wpc), BADD = increasing pair (wpc < wqc).
def pxBADU : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨7, by decide⟩ else ⟨6, by decide⟩
def pxBADD : Fin 2 → Fin 8 := fun j => if _ : j.val = 0 then ⟨6, by decide⟩ else ⟨7, by decide⟩

-- Window/param window-position-and-point sets are definable (reused by prefixes).
theorem winPTSDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) (loP hiP x₀c : R) :
    M.S 4 (fun y : Power R 4 =>
      LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wqX0C j)) 0) ((fun j : Fin 2 => y (wqX0C j)) 1) ∧
      pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
      pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
      pointSet x₀c (fun i : Fin 1 => y (wqPx0 i))) := by
  have hPlo : M.S 1 (pointSet (R := R) loP) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point loP)
  have hPhi : M.S 1 (pointSet (R := R) hiP) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point hiP)
  have hPx0 : M.S 1 (pointSet (R := R) x₀c) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point x₀c)
  exact M.inter_mem (M.reindex_mem wqPcLo M.lt_mem)
    (M.inter_mem (M.reindex_mem wqPcHi M.lt_mem)
      (M.inter_mem (M.reindex_mem wqX0C M.lt_mem)
        (M.inter_mem (M.reindex_mem wqPlo hPlo)
          (M.inter_mem (M.reindex_mem wqPhi hPhi)
            (M.reindex_mem wqPx0 hPx0)))))

-- Window/param leftward window-position-and-point sets are definable.
theorem winPTSLDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) (loP hiP x₀c : R) :
    M.S 4 (fun y : Power R 4 =>
      LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wqCX0 j)) 0) ((fun j : Fin 2 => y (wqCX0 j)) 1) ∧
      pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
      pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
      pointSet x₀c (fun i : Fin 1 => y (wqPx0 i))) := by
  have hPlo : M.S 1 (pointSet (R := R) loP) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point loP)
  have hPhi : M.S 1 (pointSet (R := R) hiP) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point hiP)
  have hPx0 : M.S 1 (pointSet (R := R) x₀c) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point x₀c)
  exact M.inter_mem (M.reindex_mem wqPcLo M.lt_mem)
    (M.inter_mem (M.reindex_mem wqPcHi M.lt_mem)
      (M.inter_mem (M.reindex_mem wqCX0 M.lt_mem)
        (M.inter_mem (M.reindex_mem wqPlo hPlo)
          (M.inter_mem (M.reindex_mem wqPhi hPhi)
            (M.reindex_mem wqPx0 hPx0)))))



-- Witness value from graph membership.
theorem wpcEqVal {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {M : OMinimalStructure R} {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a wpc : R)
    (ha : I (fun _ : Fin 1 => a))
    (hG : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
      (Power.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => wpc))) :
    wpc = (f.toFun ⟨fun _ => a, ha⟩).1 0 := by
  obtain ⟨hxp, hG'⟩ := hG
  have eR : Power.right (Power.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => wpc)) =
      (fun _ : Fin 1 => wpc) := by
    funext i
    unfold Power.right Power.append
    exact Fin.append_right _ _ _
  have eL : Power.left (Power.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => wpc)) =
      (fun _ : Fin 1 => a) := by
    funext i
    unfold Power.left Power.append
    exact Fin.append_left _ _ _
  have hsub : (⟨Power.left (Power.append (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => wpc)), hxp⟩ : {x : Power R 1 // I x}) =
      ⟨fun _ => a, ha⟩ :=
    Subtype.ext eL
  have h1 := congrArg (· 0) hG'
  rw [eR, hsub] at h1
  exact h1

-- Graph membership for append-of-constant points (witness constructor).
theorem graphAppendConst {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]    {M : OMinimalStructure R} {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a : R) (ha : I (fun _ : Fin 1 => a)) :
    FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
      (Power.append (fun _ : Fin 1 => a)
        (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0)) := by
  have hPL : Power.left (Power.append (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0)) = (fun _ : Fin 1 => a) := by
    funext i
    unfold Power.left Power.append
    exact Fin.append_left _ _ _
  have hPR : Power.right (Power.append (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0)) =
      (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0) := by
    funext i
    unfold Power.right Power.append
    exact Fin.append_right _ _ _
  have ha' : I (Power.left (Power.append (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0))) := by
    rw [hPL]
    exact ha
  refine ⟨ha', ?_⟩
  rw [hPR]
  have hsub : (⟨Power.left (Power.append (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0)), ha'⟩ :
      {x : Power R 1 // I x}) = ⟨fun _ => a, ha⟩ :=
    Subtype.ext hPL
  rw [hsub]
  funext k
  have hk : k.val = 0 := by
    have := k.isLt
    omega
  have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
  rw [ek]
  rfl





-- Rightward constancy-prefix sets are definable.
theorem constPrefixRDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (loP hiP x₀c : R) :
    M.S 1 (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
      LT.lt x₀c (Power.coord1 c) ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
        LT.lt x₀c pc ∧ LT.lt pc (Power.coord1 c) ∧
        LT.lt x₀c qc ∧ LT.lt qc (Power.coord1 c) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) := by
  have hJlo : M.S 1 (openInterval (Endpoint.finite loP) (Endpoint.finite hiP)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hPlo : M.S 1 (pointSet (R := R) loP) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point loP)
  have hPhi : M.S 1 (pointSet (R := R) hiP) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point hiP)
  have hPx0 : M.S 1 (pointSet (R := R) x₀c) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point x₀c)
  have hFwin4 : M.S 4 (fun y : Power R 4 =>
      LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => y (wqX0C j)) 0) ((fun j : Fin 2 => y (wqX0C j)) 1) ∧
      pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
      pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
      pointSet x₀c (fun i : Fin 1 => y (wqPx0 i))) :=
    M.inter_mem (M.reindex_mem wqPcLo M.lt_mem)
      (M.inter_mem (M.reindex_mem wqPcHi M.lt_mem)
        (M.inter_mem (M.reindex_mem wqX0C M.lt_mem)
          (M.inter_mem (M.reindex_mem wqPlo hPlo)
            (M.inter_mem (M.reindex_mem wqPhi hPhi)
              (M.reindex_mem wqPx0 hPx0)))))
  have hF : M.S (4 + 4) (fun q : Power R (4 + 4) =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8)))) :=
    M.inter_mem (M.reindex_mem pxIp f.domain_mem)
      (M.inter_mem (M.reindex_mem pxIq f.domain_mem)
        (M.inter_mem (M.reindex_mem pxPtLo M.lt_mem)
          (M.inter_mem (M.reindex_mem pxPtHi M.lt_mem)
            (M.inter_mem (M.reindex_mem pxQtLo M.lt_mem)
              (M.inter_mem (M.reindex_mem pxQtHi M.lt_mem)
                (M.inter_mem (M.reindex_mem pxRX0p M.lt_mem)
                  (M.inter_mem (M.reindex_mem pxRPc M.lt_mem)
                    (M.inter_mem (M.reindex_mem pxRX0q M.lt_mem)
                      (M.inter_mem (M.reindex_mem pxRQc M.lt_mem)
                        (M.inter_mem (M.reindex_mem pxGp f.graph_mem)
                          (M.inter_mem (M.reindex_mem pxGq f.graph_mem)
                            (lambdaNeqDefinable8 M))))))))))))
  have hProj1 : M.S 4 (fun y : Power R 4 => ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 4 (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.compl_mem hProj1
  have hC4 := M.inter_mem hFwin4 hC
  have hProj2 := M.existsLast_mem (n := 1) (m := 3) hC4
  have heqPR : (fun c : Power R 1 => ∃ w : Power R 3,
      setInter
      (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqX0C j)) 0) ((fun j : Fin 2 => y (wqX0C j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i)))
      (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t))
      (Power.append c w))
      = (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
        LT.lt x₀c (Power.coord1 c) ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
          LT.lt x₀c pc ∧ LT.lt pc (Power.coord1 c) ∧
          LT.lt x₀c qc ∧ LT.lt qc (Power.coord1 c) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) := by
    funext c
    apply propext
    constructor
    · intro h
      obtain ⟨w, hWIN, hNEG⟩ := h
      obtain ⟨hPcLo, hPcHi, hX0C, hPlo, hPhi, hPx0⟩ := hWIN
      have eLo : w (⟨0, by decide⟩ : Fin 3) = loP := hPlo
      have eHi : w (⟨1, by decide⟩ : Fin 3) = hiP := hPhi
      have eX0 : w (⟨2, by decide⟩ : Fin 3) = x₀c := hPx0
      have gPcLo : LT.lt loP (Power.coord1 c) := by
        have h' : LT.lt (w (⟨0, by decide⟩ : Fin 3)) (Power.coord1 c) := hPcLo
        rw [eLo] at h'
        exact h'
      have gPcHi : LT.lt (Power.coord1 c) hiP := by
        have h' : LT.lt (Power.coord1 c) (w (⟨1, by decide⟩ : Fin 3)) := hPcHi
        rw [eHi] at h'
        exact h'
      have gX0C : LT.lt x₀c (Power.coord1 c) := by
        have h' : LT.lt (w (⟨2, by decide⟩ : Fin 3)) (Power.coord1 c) := hX0C
        rw [eX0] at h'
        exact h'
      refine ⟨⟨gPcLo, gPcHi⟩, gX0C, ?_⟩
      intro hex
      apply hNEG
      obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hRp1, hRp2, hRq1, hRq2, hGp, hGq, hne⟩ := hex
      refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
        else if k = (⟨1, by decide⟩ : Fin 4) then qc
        else if k = (⟨2, by decide⟩ : Fin 4) then wpc
        else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hIp
      · exact hIq
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) pc
        rw [eLo]
        exact hJp.left
      · show LT.lt pc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJp.right
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) qc
        rw [eLo]
        exact hJq.left
      · show LT.lt qc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJq.right
      · show LT.lt (w (⟨2, by decide⟩ : Fin 3)) pc
        rw [eX0]
        exact hRp1
      · exact hRp2
      · show LT.lt (w (⟨2, by decide⟩ : Fin 3)) qc
        rw [eX0]
        exact hRq1
      · exact hRq2
      · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGp j))
          = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGp]
        exact hGp
      · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGq j))
          = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGq]
        exact hGq
      · exact hne
    · intro h
      obtain ⟨hJy, hX0, hNEG⟩ := h
      refine ⟨(fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
        else if k = (⟨1, by decide⟩ : Fin 3) then hiP
        else x₀c), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · have e : LT.lt loP (Power.coord1 c) := hJy.left
          exact e
        · have e : LT.lt (Power.coord1 c) hiP := hJy.right
          exact e
        · have e : LT.lt x₀c (Power.coord1 c) := hX0
          exact e
        · have e : (Power.append c (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
            else if k = (⟨1, by decide⟩ : Fin 3) then hiP
            else x₀c)) (⟨1, by decide⟩ : Fin 4) = loP := rfl
          exact e
        · have e : (Power.append c (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
            else if k = (⟨1, by decide⟩ : Fin 3) then hiP
            else x₀c)) (⟨2, by decide⟩ : Fin 4) = hiP := rfl
          exact e
        · have e : (Power.append c (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
            else if k = (⟨1, by decide⟩ : Fin 3) then hiP
            else x₀c)) (⟨3, by decide⟩ : Fin 4) = x₀c := rfl
          exact e
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hRp1, hRp2, hRq1, hRq2, hGp, hGq, hBAD⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hRp1
        · exact hRp2
        · exact hRq1
        · exact hRq2
        · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · exact hBAD
  rw [← heqPR]
  exact hProj2

-- Leftward constancy-prefix sets are definable.
theorem constPrefixLDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (loP hiP x₀c : R) :
    M.S 1 (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
      LT.lt (Power.coord1 c) x₀c ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
        LT.lt (Power.coord1 c) pc ∧ LT.lt pc x₀c ∧
        LT.lt (Power.coord1 c) qc ∧ LT.lt qc x₀c ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) := by
  have hF : M.S (4 + 4) (fun q : Power R (4 + 4) =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8)))) :=
    M.inter_mem (M.reindex_mem pxIp f.domain_mem)
      (M.inter_mem (M.reindex_mem pxIq f.domain_mem)
        (M.inter_mem (M.reindex_mem pxPtLo M.lt_mem)
          (M.inter_mem (M.reindex_mem pxPtHi M.lt_mem)
            (M.inter_mem (M.reindex_mem pxQtLo M.lt_mem)
              (M.inter_mem (M.reindex_mem pxQtHi M.lt_mem)
                (M.inter_mem (M.reindex_mem pxCPc M.lt_mem)
                  (M.inter_mem (M.reindex_mem pxPcX0 M.lt_mem)
                    (M.inter_mem (M.reindex_mem pxCQc M.lt_mem)
                      (M.inter_mem (M.reindex_mem pxQcX0 M.lt_mem)
                        (M.inter_mem (M.reindex_mem pxGp f.graph_mem)
                          (M.inter_mem (M.reindex_mem pxGq f.graph_mem)
                            (lambdaNeqDefinable8 M))))))))))))
  have hProj1 : M.S 4 (fun y : Power R 4 => ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 4 (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.compl_mem hProj1
  have hC4 : M.S 4 (setInter
      (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqCX0 j)) 0) ((fun j : Fin 2 => y (wqCX0 j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i)))
      (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t))) := by
    have hFwin4L : M.S 4 (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqCX0 j)) 0) ((fun j : Fin 2 => y (wqCX0 j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i))) := by
      have hPlo : M.S 1 (pointSet (R := R) loP) :=
        (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point loP)
      have hPhi : M.S 1 (pointSet (R := R) hiP) :=
        (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point hiP)
      have hPx0 : M.S 1 (pointSet (R := R) x₀c) :=
        (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point x₀c)
      exact M.inter_mem (M.reindex_mem wqPcLo M.lt_mem)
        (M.inter_mem (M.reindex_mem wqPcHi M.lt_mem)
          (M.inter_mem (M.reindex_mem wqCX0 M.lt_mem)
            (M.inter_mem (M.reindex_mem wqPlo hPlo)
              (M.inter_mem (M.reindex_mem wqPhi hPhi)
                (M.reindex_mem wqPx0 hPx0)))))
    exact M.inter_mem hFwin4L hC
  have hProj2 := M.existsLast_mem (n := 1) (m := 3) hC4
  have heqPL : (fun c : Power R 1 => ∃ w : Power R 3,
      setInter
      (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqCX0 j)) 0) ((fun j : Fin 2 => y (wqCX0 j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i)))
      (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      ¬ ((fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t))
      (Power.append c w))
      = (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
        LT.lt (Power.coord1 c) x₀c ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
          LT.lt (Power.coord1 c) pc ∧ LT.lt pc x₀c ∧
          LT.lt (Power.coord1 c) qc ∧ LT.lt qc x₀c ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) := by
    funext c
    apply propext
    constructor
    · intro h
      obtain ⟨w, hWIN, hNEG⟩ := h
      obtain ⟨hPcLo, hPcHi, hCX0, hPlo, hPhi, hPx0⟩ := hWIN
      have eLo : w (⟨0, by decide⟩ : Fin 3) = loP := hPlo
      have eHi : w (⟨1, by decide⟩ : Fin 3) = hiP := hPhi
      have eX0 : w (⟨2, by decide⟩ : Fin 3) = x₀c := hPx0
      have gPcLo : LT.lt loP (Power.coord1 c) := by
        have h' : LT.lt (w (⟨0, by decide⟩ : Fin 3)) (Power.coord1 c) := hPcLo
        rw [eLo] at h'
        exact h'
      have gPcHi : LT.lt (Power.coord1 c) hiP := by
        have h' : LT.lt (Power.coord1 c) (w (⟨1, by decide⟩ : Fin 3)) := hPcHi
        rw [eHi] at h'
        exact h'
      have gCX0 : LT.lt (Power.coord1 c) x₀c := by
        have h' : LT.lt (Power.coord1 c) (w (⟨2, by decide⟩ : Fin 3)) := hCX0
        rw [eX0] at h'
        exact h'
      refine ⟨⟨gPcLo, gPcHi⟩, gCX0, ?_⟩
      intro hex
      apply hNEG
      obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hCp, hPx, hCq, hQx, hGp, hGq, hne⟩ := hex
      refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
        else if k = (⟨1, by decide⟩ : Fin 4) then qc
        else if k = (⟨2, by decide⟩ : Fin 4) then wpc
        else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hIp
      · exact hIq
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) pc
        rw [eLo]
        exact hJp.left
      · show LT.lt pc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJp.right
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) qc
        rw [eLo]
        exact hJq.left
      · show LT.lt qc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJq.right
      · exact hCp
      · show LT.lt pc (w (⟨2, by decide⟩ : Fin 3))
        rw [eX0]
        exact hPx
      · exact hCq
      · show LT.lt qc (w (⟨2, by decide⟩ : Fin 3))
        rw [eX0]
        exact hQx
      · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGp j))
          = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGp]
        exact hGp
      · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGq j))
          = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGq]
        exact hGq
      · exact hne
    · intro h
      obtain ⟨hJy, hX0, hNEG⟩ := h
      refine ⟨(fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
        else if k = (⟨1, by decide⟩ : Fin 3) then hiP
        else x₀c), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hJy.left
        · exact hJy.right
        · exact hX0
        · rfl
        · rfl
        · rfl
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hCp, hPx, hCq, hQx, hGp, hGq, hBAD⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hCp
        · exact hPx
        · exact hCq
        · exact hQx
        · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · exact hBAD
  rw [← heqPL]
  exact hProj2

-- Rightward increasing-prefix sets are definable.
theorem incPrefixRDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (loP hiP x₀c : R) :
    M.S 1 (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
      LT.lt x₀c (Power.coord1 c) ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
        LT.lt x₀c pc ∧ LT.lt pc (Power.coord1 c) ∧
        LT.lt x₀c qc ∧ LT.lt qc (Power.coord1 c) ∧
        LT.lt pc qc ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
          ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
  have hF : M.S (4 + 4) (fun q : Power R (4 + 4) =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8)))) :=
    M.inter_mem (M.reindex_mem pxIp f.domain_mem)
      (M.inter_mem (M.reindex_mem pxIq f.domain_mem)
        (M.inter_mem (M.reindex_mem pxPtLo M.lt_mem)
          (M.inter_mem (M.reindex_mem pxPtHi M.lt_mem)
            (M.inter_mem (M.reindex_mem pxQtLo M.lt_mem)
              (M.inter_mem (M.reindex_mem pxQtHi M.lt_mem)
                (M.inter_mem (M.reindex_mem pxRX0p M.lt_mem)
                  (M.inter_mem (M.reindex_mem pxRPc M.lt_mem)
                    (M.inter_mem (M.reindex_mem pxRX0q M.lt_mem)
                      (M.inter_mem (M.reindex_mem pxRQc M.lt_mem)
                        (M.inter_mem (M.reindex_mem pxLTpq M.lt_mem)
                          (M.inter_mem (M.reindex_mem pxGp f.graph_mem)
                            (M.inter_mem (M.reindex_mem pxGq f.graph_mem)
                              (M.union_mem (M.reindex_mem pxBADU M.lt_mem)
                                (lambdaEqDefinable8 M))))))))))))))
  have hProj1 : M.S 4 (fun y : Power R 4 => ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 4 (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.compl_mem hProj1
  have hC4 := M.inter_mem (winPTSDefinable M loP hiP x₀c) hC
  have hProj2 := M.existsLast_mem (n := 1) (m := 3) hC4
  have heqUR : (fun c : Power R 1 => ∃ w : Power R 3,
      setInter
      (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqX0C j)) 0) ((fun j : Fin 2 => y (wqX0C j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i)))
      (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t))
      (Power.append c w))
      = (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
        LT.lt x₀c (Power.coord1 c) ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
          LT.lt x₀c pc ∧ LT.lt pc (Power.coord1 c) ∧
          LT.lt x₀c qc ∧ LT.lt qc (Power.coord1 c) ∧
          LT.lt pc qc ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
            ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
    funext c
    apply propext
    constructor
    · intro h
      obtain ⟨w, hWIN, hNEG⟩ := h
      obtain ⟨hPcLo, hPcHi, hX0C, hPlo, hPhi, hPx0⟩ := hWIN
      have eLo : w (⟨0, by decide⟩ : Fin 3) = loP := hPlo
      have eHi : w (⟨1, by decide⟩ : Fin 3) = hiP := hPhi
      have eX0 : w (⟨2, by decide⟩ : Fin 3) = x₀c := hPx0
      have gPcLo : LT.lt loP (Power.coord1 c) := by
        have h' : LT.lt (w (⟨0, by decide⟩ : Fin 3)) (Power.coord1 c) := hPcLo
        rw [eLo] at h'
        exact h'
      have gPcHi : LT.lt (Power.coord1 c) hiP := by
        have h' : LT.lt (Power.coord1 c) (w (⟨1, by decide⟩ : Fin 3)) := hPcHi
        rw [eHi] at h'
        exact h'
      have gX0C : LT.lt x₀c (Power.coord1 c) := by
        have h' : LT.lt (w (⟨2, by decide⟩ : Fin 3)) (Power.coord1 c) := hX0C
        rw [eX0] at h'
        exact h'
      refine ⟨⟨gPcLo, gPcHi⟩, gX0C, ?_⟩
      intro hex
      apply hNEG
      obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hRp1, hRp2, hRq1, hRq2, hLT, hGp, hGq, hbadU⟩ := hex
      refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
        else if k = (⟨1, by decide⟩ : Fin 4) then qc
        else if k = (⟨2, by decide⟩ : Fin 4) then wpc
        else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hIp
      · exact hIq
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) pc
        rw [eLo]
        exact hJp.left
      · show LT.lt pc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJp.right
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) qc
        rw [eLo]
        exact hJq.left
      · show LT.lt qc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJq.right
      · show LT.lt (w (⟨2, by decide⟩ : Fin 3)) pc
        rw [eX0]
        exact hRp1
      · exact hRp2
      · show LT.lt (w (⟨2, by decide⟩ : Fin 3)) qc
        rw [eX0]
        exact hRq1
      · exact hRq2
      · exact hLT
      · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGp j))
          = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGp]
        exact hGp
      · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGq j))
          = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGq]
        exact hGq
      · exact hbadU
    · intro h
      obtain ⟨hJy, hX0, hNEG⟩ := h
      refine ⟨(fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
        else if k = (⟨1, by decide⟩ : Fin 3) then hiP
        else x₀c), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hJy.left
        · exact hJy.right
        · exact hX0
        · rfl
        · rfl
        · rfl
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hRp1, hRp2, hRq1, hRq2, hLT, hGp, hGq, hBADU⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hRp1
        · exact hRp2
        · exact hRq1
        · exact hRq2
        · exact hLT
        · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · exact hBADU
  rw [← heqUR]
  exact hProj2

-- Leftward increasing-prefix sets are definable.
theorem incPrefixLDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (loP hiP x₀c : R) :
    M.S 1 (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
      LT.lt (Power.coord1 c) x₀c ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
        LT.lt (Power.coord1 c) pc ∧ LT.lt pc x₀c ∧
        LT.lt (Power.coord1 c) qc ∧ LT.lt qc x₀c ∧
        LT.lt pc qc ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
          ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
  have hF : M.S (4 + 4) (fun q : Power R (4 + 4) =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8)))) :=
    M.inter_mem (M.reindex_mem pxIp f.domain_mem)
      (M.inter_mem (M.reindex_mem pxIq f.domain_mem)
        (M.inter_mem (M.reindex_mem pxPtLo M.lt_mem)
          (M.inter_mem (M.reindex_mem pxPtHi M.lt_mem)
            (M.inter_mem (M.reindex_mem pxQtLo M.lt_mem)
              (M.inter_mem (M.reindex_mem pxQtHi M.lt_mem)
                (M.inter_mem (M.reindex_mem pxCPc M.lt_mem)
                  (M.inter_mem (M.reindex_mem pxPcX0 M.lt_mem)
                    (M.inter_mem (M.reindex_mem pxCQc M.lt_mem)
                      (M.inter_mem (M.reindex_mem pxQcX0 M.lt_mem)
                        (M.inter_mem (M.reindex_mem pxLTpq M.lt_mem)
                          (M.inter_mem (M.reindex_mem pxGp f.graph_mem)
                            (M.inter_mem (M.reindex_mem pxGq f.graph_mem)
                              (M.union_mem (M.reindex_mem pxBADU M.lt_mem)
                                (lambdaEqDefinable8 M))))))))))))))
  have hProj1 : M.S 4 (fun y : Power R 4 => ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 4 (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.compl_mem hProj1
  have hC4 := M.inter_mem (winPTSLDefinable M loP hiP x₀c) hC
  have hProj2 := M.existsLast_mem (n := 1) (m := 3) hC4
  have heqUL : (fun c : Power R 1 => ∃ w : Power R 3,
      setInter
      (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqCX0 j)) 0) ((fun j : Fin 2 => y (wqCX0 j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i)))
      (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADU j)) 0) ((fun j : Fin 2 => q (pxBADU j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t))
      (Power.append c w))
      = (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
        LT.lt (Power.coord1 c) x₀c ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
          LT.lt (Power.coord1 c) pc ∧ LT.lt pc x₀c ∧
          LT.lt (Power.coord1 c) qc ∧ LT.lt qc x₀c ∧
          LT.lt pc qc ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
            ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
    funext c
    apply propext
    constructor
    · intro h
      obtain ⟨w, hWIN, hNEG⟩ := h
      obtain ⟨hPcLo, hPcHi, hCX0, hPlo, hPhi, hPx0⟩ := hWIN
      have eLo : w (⟨0, by decide⟩ : Fin 3) = loP := hPlo
      have eHi : w (⟨1, by decide⟩ : Fin 3) = hiP := hPhi
      have eX0 : w (⟨2, by decide⟩ : Fin 3) = x₀c := hPx0
      have gPcLo : LT.lt loP (Power.coord1 c) := by
        have h' : LT.lt (w (⟨0, by decide⟩ : Fin 3)) (Power.coord1 c) := hPcLo
        rw [eLo] at h'
        exact h'
      have gPcHi : LT.lt (Power.coord1 c) hiP := by
        have h' : LT.lt (Power.coord1 c) (w (⟨1, by decide⟩ : Fin 3)) := hPcHi
        rw [eHi] at h'
        exact h'
      have gCX0 : LT.lt (Power.coord1 c) x₀c := by
        have h' : LT.lt (Power.coord1 c) (w (⟨2, by decide⟩ : Fin 3)) := hCX0
        rw [eX0] at h'
        exact h'
      refine ⟨⟨gPcLo, gPcHi⟩, gCX0, ?_⟩
      intro hex
      apply hNEG
      obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hCp, hPx, hCq, hQx, hLT, hGp, hGq, hbadU⟩ := hex
      refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
        else if k = (⟨1, by decide⟩ : Fin 4) then qc
        else if k = (⟨2, by decide⟩ : Fin 4) then wpc
        else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hIp
      · exact hIq
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) pc
        rw [eLo]
        exact hJp.left
      · show LT.lt pc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJp.right
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) qc
        rw [eLo]
        exact hJq.left
      · show LT.lt qc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJq.right
      · exact hCp
      · show LT.lt pc (w (⟨2, by decide⟩ : Fin 3))
        rw [eX0]
        exact hPx
      · exact hCq
      · show LT.lt qc (w (⟨2, by decide⟩ : Fin 3))
        rw [eX0]
        exact hQx
      · exact hLT
      · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGp j))
          = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGp]
        exact hGp
      · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGq j))
          = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGq]
        exact hGq
      · exact hbadU
    · intro h
      obtain ⟨hJy, hX0, hNEG⟩ := h
      refine ⟨(fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
        else if k = (⟨1, by decide⟩ : Fin 3) then hiP
        else x₀c), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hJy.left
        · exact hJy.right
        · exact hX0
        · rfl
        · rfl
        · rfl
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hCp, hPx, hCq, hQx, hLT, hGp, hGq, hBADU⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hCp
        · exact hPx
        · exact hCq
        · exact hQx
        · exact hLT
        · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · exact hBADU
  rw [← heqUL]
  exact hProj2

-- Rightward decreasing-prefix sets are definable.
theorem decPrefixRDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (loP hiP x₀c : R) :
    M.S 1 (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
      LT.lt x₀c (Power.coord1 c) ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
        LT.lt x₀c pc ∧ LT.lt pc (Power.coord1 c) ∧
        LT.lt x₀c qc ∧ LT.lt qc (Power.coord1 c) ∧
        LT.lt pc qc ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
          ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
  have hF : M.S (4 + 4) (fun q : Power R (4 + 4) =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8)))) :=
    M.inter_mem (M.reindex_mem pxIp f.domain_mem)
      (M.inter_mem (M.reindex_mem pxIq f.domain_mem)
        (M.inter_mem (M.reindex_mem pxPtLo M.lt_mem)
          (M.inter_mem (M.reindex_mem pxPtHi M.lt_mem)
            (M.inter_mem (M.reindex_mem pxQtLo M.lt_mem)
              (M.inter_mem (M.reindex_mem pxQtHi M.lt_mem)
                (M.inter_mem (M.reindex_mem pxRX0p M.lt_mem)
                  (M.inter_mem (M.reindex_mem pxRPc M.lt_mem)
                    (M.inter_mem (M.reindex_mem pxRX0q M.lt_mem)
                      (M.inter_mem (M.reindex_mem pxRQc M.lt_mem)
                        (M.inter_mem (M.reindex_mem pxLTpq M.lt_mem)
                          (M.inter_mem (M.reindex_mem pxGp f.graph_mem)
                            (M.inter_mem (M.reindex_mem pxGq f.graph_mem)
                              (M.union_mem (M.reindex_mem pxBADD M.lt_mem)
                                (lambdaEqDefinable8 M))))))))))))))
  have hProj1 : M.S 4 (fun y : Power R 4 => ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 4 (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.compl_mem hProj1
  have hC4 := M.inter_mem (winPTSDefinable M loP hiP x₀c) hC
  have hProj2 := M.existsLast_mem (n := 1) (m := 3) hC4
  have heqDR : (fun c : Power R 1 => ∃ w : Power R 3,
      setInter
      (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqX0C j)) 0) ((fun j : Fin 2 => y (wqX0C j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i)))
      (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0p j)) 0) ((fun j : Fin 2 => q (pxRX0p j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRPc j)) 0) ((fun j : Fin 2 => q (pxRPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRX0q j)) 0) ((fun j : Fin 2 => q (pxRX0q j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxRQc j)) 0) ((fun j : Fin 2 => q (pxRQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t))
      (Power.append c w))
      = (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
        LT.lt x₀c (Power.coord1 c) ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
          LT.lt x₀c pc ∧ LT.lt pc (Power.coord1 c) ∧
          LT.lt x₀c qc ∧ LT.lt qc (Power.coord1 c) ∧
          LT.lt pc qc ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
            ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
    funext c
    apply propext
    constructor
    · intro h
      obtain ⟨w, hWIN, hNEG⟩ := h
      obtain ⟨hPcLo, hPcHi, hX0C, hPlo, hPhi, hPx0⟩ := hWIN
      have eLo : w (⟨0, by decide⟩ : Fin 3) = loP := hPlo
      have eHi : w (⟨1, by decide⟩ : Fin 3) = hiP := hPhi
      have eX0 : w (⟨2, by decide⟩ : Fin 3) = x₀c := hPx0
      have gPcLo : LT.lt loP (Power.coord1 c) := by
        have h' : LT.lt (w (⟨0, by decide⟩ : Fin 3)) (Power.coord1 c) := hPcLo
        rw [eLo] at h'
        exact h'
      have gPcHi : LT.lt (Power.coord1 c) hiP := by
        have h' : LT.lt (Power.coord1 c) (w (⟨1, by decide⟩ : Fin 3)) := hPcHi
        rw [eHi] at h'
        exact h'
      have gX0C : LT.lt x₀c (Power.coord1 c) := by
        have h' : LT.lt (w (⟨2, by decide⟩ : Fin 3)) (Power.coord1 c) := hX0C
        rw [eX0] at h'
        exact h'
      refine ⟨⟨gPcLo, gPcHi⟩, gX0C, ?_⟩
      intro hex
      apply hNEG
      obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hRp1, hRp2, hRq1, hRq2, hLT, hGp, hGq, hbadD⟩ := hex
      refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
        else if k = (⟨1, by decide⟩ : Fin 4) then qc
        else if k = (⟨2, by decide⟩ : Fin 4) then wpc
        else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hIp
      · exact hIq
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) pc
        rw [eLo]
        exact hJp.left
      · show LT.lt pc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJp.right
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) qc
        rw [eLo]
        exact hJq.left
      · show LT.lt qc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJq.right
      · show LT.lt (w (⟨2, by decide⟩ : Fin 3)) pc
        rw [eX0]
        exact hRp1
      · exact hRp2
      · show LT.lt (w (⟨2, by decide⟩ : Fin 3)) qc
        rw [eX0]
        exact hRq1
      · exact hRq2
      · exact hLT
      · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGp j))
          = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGp]
        exact hGp
      · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGq j))
          = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGq]
        exact hGq
      · exact hbadD
    · intro h
      obtain ⟨hJy, hX0, hNEG⟩ := h
      refine ⟨(fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
        else if k = (⟨1, by decide⟩ : Fin 3) then hiP
        else x₀c), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hJy.left
        · exact hJy.right
        · exact hX0
        · rfl
        · rfl
        · rfl
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hRp1, hRp2, hRq1, hRq2, hLT, hGp, hGq, hBADD⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hRp1
        · exact hRp2
        · exact hRq1
        · exact hRq2
        · exact hLT
        · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · exact hBADD
  rw [← heqDR]
  exact hProj2

-- Leftward decreasing-prefix sets are definable.
theorem decPrefixLDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (loP hiP x₀c : R) :
    M.S 1 (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
      LT.lt (Power.coord1 c) x₀c ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
        openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
        LT.lt (Power.coord1 c) pc ∧ LT.lt pc x₀c ∧
        LT.lt (Power.coord1 c) qc ∧ LT.lt qc x₀c ∧
        LT.lt pc qc ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
          ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
  have hF : M.S (4 + 4) (fun q : Power R (4 + 4) =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8)))) :=
    M.inter_mem (M.reindex_mem pxIp f.domain_mem)
      (M.inter_mem (M.reindex_mem pxIq f.domain_mem)
        (M.inter_mem (M.reindex_mem pxPtLo M.lt_mem)
          (M.inter_mem (M.reindex_mem pxPtHi M.lt_mem)
            (M.inter_mem (M.reindex_mem pxQtLo M.lt_mem)
              (M.inter_mem (M.reindex_mem pxQtHi M.lt_mem)
                (M.inter_mem (M.reindex_mem pxCPc M.lt_mem)
                  (M.inter_mem (M.reindex_mem pxPcX0 M.lt_mem)
                    (M.inter_mem (M.reindex_mem pxCQc M.lt_mem)
                      (M.inter_mem (M.reindex_mem pxQcX0 M.lt_mem)
                        (M.inter_mem (M.reindex_mem pxLTpq M.lt_mem)
                          (M.inter_mem (M.reindex_mem pxGp f.graph_mem)
                            (M.inter_mem (M.reindex_mem pxGq f.graph_mem)
                              (M.union_mem (M.reindex_mem pxBADD M.lt_mem)
                                (lambdaEqDefinable8 M))))))))))))))
  have hProj1 : M.S 4 (fun y : Power R 4 => ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 4 (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t)) :=
    M.compl_mem hProj1
  have hC4 := M.inter_mem (winPTSLDefinable M loP hiP x₀c) hC
  have hProj2 := M.existsLast_mem (n := 1) (m := 3) hC4
  have heqDL : (fun c : Power R 1 => ∃ w : Power R 3,
      setInter
      (fun y : Power R 4 =>
        LT.lt ((fun j : Fin 2 => y (wqPcLo j)) 0) ((fun j : Fin 2 => y (wqPcLo j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqPcHi j)) 0) ((fun j : Fin 2 => y (wqPcHi j)) 1) ∧
        LT.lt ((fun j : Fin 2 => y (wqCX0 j)) 0) ((fun j : Fin 2 => y (wqCX0 j)) 1) ∧
        pointSet loP (fun i : Fin 1 => y (wqPlo i)) ∧
        pointSet hiP (fun i : Fin 1 => y (wqPhi i)) ∧
        pointSet x₀c (fun i : Fin 1 => y (wqPx0 i)))
      (fun y : Power R 4 => ¬ ∃ t : Power R 4,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (pxIp i)) ∧
      I (fun i : Fin 1 => q (pxIq i)) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtLo j)) 0) ((fun j : Fin 2 => q (pxPtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPtHi j)) 0) ((fun j : Fin 2 => q (pxPtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtLo j)) 0) ((fun j : Fin 2 => q (pxQtLo j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQtHi j)) 0) ((fun j : Fin 2 => q (pxQtHi j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCPc j)) 0) ((fun j : Fin 2 => q (pxCPc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxPcX0 j)) 0) ((fun j : Fin 2 => q (pxPcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxCQc j)) 0) ((fun j : Fin 2 => q (pxCQc j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxQcX0 j)) 0) ((fun j : Fin 2 => q (pxQcX0 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (pxLTpq j)) 0) ((fun j : Fin 2 => q (pxLTpq j)) 1) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGp j)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (pxGq j)) ∧
      (LT.lt ((fun j : Fin 2 => q (pxBADD j)) 0) ((fun j : Fin 2 => q (pxBADD j)) 1) ∨
      (fun _ : Fin 1 => q (⟨6, by decide⟩ : Fin 8)) =
        (fun _ : Fin 1 => q (⟨7, by decide⟩ : Fin 8))))
        (Power.append y t))
      (Power.append c w))
      = (fun c : Power R 1 => openInterval (Endpoint.finite loP) (Endpoint.finite hiP) c ∧
        LT.lt (Power.coord1 c) x₀c ∧
        ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => pc) ∧
          openInterval (Endpoint.finite loP) (Endpoint.finite hiP) (fun _ => qc) ∧
          LT.lt (Power.coord1 c) pc ∧ LT.lt pc x₀c ∧
          LT.lt (Power.coord1 c) qc ∧ LT.lt qc x₀c ∧
          LT.lt pc qc ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => pc) (fun _ => wpc)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ => qc) (fun _ => wqc)) ∧
          (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
            ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) := by
    funext c
    apply propext
    constructor
    · intro h
      obtain ⟨w, hWIN, hNEG⟩ := h
      obtain ⟨hPcLo, hPcHi, hCX0, hPlo, hPhi, hPx0⟩ := hWIN
      have eLo : w (⟨0, by decide⟩ : Fin 3) = loP := hPlo
      have eHi : w (⟨1, by decide⟩ : Fin 3) = hiP := hPhi
      have eX0 : w (⟨2, by decide⟩ : Fin 3) = x₀c := hPx0
      have gPcLo : LT.lt loP (Power.coord1 c) := by
        have h' : LT.lt (w (⟨0, by decide⟩ : Fin 3)) (Power.coord1 c) := hPcLo
        rw [eLo] at h'
        exact h'
      have gPcHi : LT.lt (Power.coord1 c) hiP := by
        have h' : LT.lt (Power.coord1 c) (w (⟨1, by decide⟩ : Fin 3)) := hPcHi
        rw [eHi] at h'
        exact h'
      have gCX0 : LT.lt (Power.coord1 c) x₀c := by
        have h' : LT.lt (Power.coord1 c) (w (⟨2, by decide⟩ : Fin 3)) := hCX0
        rw [eX0] at h'
        exact h'
      refine ⟨⟨gPcLo, gPcHi⟩, gCX0, ?_⟩
      intro hex
      apply hNEG
      obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hCp, hPx, hCq, hQx, hLT, hGp, hGq, hbadD⟩ := hex
      refine ⟨(fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
        else if k = (⟨1, by decide⟩ : Fin 4) then qc
        else if k = (⟨2, by decide⟩ : Fin 4) then wpc
        else wqc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hIp
      · exact hIq
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) pc
        rw [eLo]
        exact hJp.left
      · show LT.lt pc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJp.right
      · show LT.lt (w (⟨0, by decide⟩ : Fin 3)) qc
        rw [eLo]
        exact hJq.left
      · show LT.lt qc (w (⟨1, by decide⟩ : Fin 3))
        rw [eHi]
        exact hJq.right
      · exact hCp
      · show LT.lt pc (w (⟨2, by decide⟩ : Fin 3))
        rw [eX0]
        exact hPx
      · exact hCq
      · show LT.lt qc (w (⟨2, by decide⟩ : Fin 3))
        rw [eX0]
        exact hQx
      · exact hLT
      · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGp j))
          = Power.append (fun _ : Fin 1 => pc) (fun _ : Fin 1 => wpc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGp]
        exact hGp
      · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c w)
            (fun k : Fin 4 => if k = (⟨0, by decide⟩ : Fin 4) then pc
            else if k = (⟨1, by decide⟩ : Fin 4) then qc
            else if k = (⟨2, by decide⟩ : Fin 4) then wpc
            else wqc)) (pxGq j))
          = Power.append (fun _ : Fin 1 => qc) (fun _ : Fin 1 => wqc) := by
          funext j
          have hiv : j.val < 1 + 1 := j.isLt
          by_cases hj : j.val = 0
          · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
            rw [hj0]
            rfl
          · have hj1 : j.val = 1 := by omega
            have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
            rw [hj1']
            rfl
        rw [eGq]
        exact hGq
      · exact hbadD
    · intro h
      obtain ⟨hJy, hX0, hNEG⟩ := h
      refine ⟨(fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
        else if k = (⟨1, by decide⟩ : Fin 3) then hiP
        else x₀c), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hJy.left
        · exact hJy.right
        · exact hX0
        · rfl
        · rfl
        · rfl
      · intro hex
        apply hNEG
        obtain ⟨t, hIp, hIq, hJp1, hJp2, hJq1, hJq2, hCp, hPx, hCq, hQx, hLT, hGp, hGq, hBADD⟩ := hex
        refine ⟨(t (⟨0, by decide⟩ : Fin 4)),
          (t (⟨1, by decide⟩ : Fin 4)),
          (t (⟨2, by decide⟩ : Fin 4)),
          (t (⟨3, by decide⟩ : Fin 4)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hIp
        · exact hIq
        · exact ⟨hJp1, hJp2⟩
        · exact ⟨hJq1, hJq2⟩
        · exact hCp
        · exact hPx
        · exact hCq
        · exact hQx
        · exact hLT
        · have eGp : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGp j))
            = Power.append (fun _ : Fin 1 => (t (⟨0, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨2, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGp]
          exact hGp
        · have eGq : (fun j : Fin (1 + 1) => (Power.append (Power.append c
              (fun k : Fin 3 => if k = (⟨0, by decide⟩ : Fin 3) then loP
              else if k = (⟨1, by decide⟩ : Fin 3) then hiP
              else x₀c)) t) (pxGq j))
            = Power.append (fun _ : Fin 1 => (t (⟨1, by decide⟩ : Fin 4)))
              (fun _ : Fin 1 => (t (⟨3, by decide⟩ : Fin 4))) := by
            funext j
            have hiv : j.val < 1 + 1 := j.isLt
            by_cases hj : j.val = 0
            · have hj0 : j = (⟨0, by decide⟩ : Fin (1 + 1)) := Fin.ext hj
              rw [hj0]
              rfl
            · have hj1 : j.val = 1 := by omega
              have hj1' : j = (⟨1, by decide⟩ : Fin (1 + 1)) := Fin.ext hj1
              rw [hj1']
              rfl
          rw [← eGq]
          exact hGq
        · exact hBADD
  rw [← heqDL]
  exact hProj2

-- Membership gives a Fin index.
theorem memGetAux {R : Type} (L : List R) (c : R) (h : c ∈ L) :
    ∃ i : Fin L.length, L.get i = c := by
  induction L with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with h | h
    · refine ⟨⟨0, by simp⟩, ?_⟩
      simp
      exact h.symm
    · obtain ⟨i, hi⟩ := ih h
      have hiv : i.val < ys.length := i.isLt
      refine ⟨⟨i.val + 1, by show i.val + 1 < ys.length + 1; omega⟩, ?_⟩
      simp
      exact hi

-- Order along sorted-list indices.
theorem sortedGetLT {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (Srt : List R) (hS : SortedLT Srt) (i j : Fin Srt.length) (hij : i.val < j.val) :
    LT.lt (Srt.get i) (Srt.get j) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hij
  have hlen : i.val + (d + 1) < Srt.length := hd ▸ j.isLt
  have ch := sortedChainAux Srt hS i.val d hlen
  have e1 : (⟨i.val + (d + 1), hlen⟩ : Fin Srt.length) = j := by
    apply Fin.ext
    show i.val + (d + 1) = j.val
    exact hd.symm
  rw [← e1]
  exact ch

namespace Monotonicity_Theorem

def IsLowerBound1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (b : R) : Prop :=
  ∀ x : Power R 1, A x → (LT.lt b (Power.coord1 x) ∨ Power.coord1 x = b)

def BoundedBelow1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) : Prop :=
  ∃ b : R, IsLowerBound1 A b

def IsInfimum1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (s : R) : Prop :=
  IsLowerBound1 A s ∧
  ∀ b : R, IsLowerBound1 A b → (LT.lt b s ∨ b = s)

noncomputable def min1 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : R) : R :=
  if LT.lt a b then a else b

theorem notLBofGreatest {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (m : R)
    (hGreatest : ∀ bnd, IsLowerBound1 A bnd → (LT.lt bnd m ∨ bnd = m))
    (t : R) (htm : LT.lt m t) : ∃ s, A s ∧ LT.lt (Power.coord1 s) t := by
  by_contra hne
  have htLB : IsLowerBound1 A t := by
    intro s hs
    rcases lt_trichotomy (Power.coord1 s) t with h | h | h
    · have hlt := h
      exact False.elim (hne ⟨s, hs, hlt⟩)
    · have heq := h
      exact Or.inr heq
    · have hlt := h
      exact Or.inl hlt
  rcases hGreatest t htLB with h | h
  · exact lt_irrefl _ (lt_trans h htm)
  · rw [h] at htm
    exact lt_irrefl _ htm

end Monotonicity_Theorem

open Monotonicity_Theorem

theorem infUnionAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A B : Set (Power R 1)) (sA sB : R)
    (hInfA : IsInfimum1 A sA)
    (hInfB : IsInfimum1 B sB) :
    IsInfimum1 ((A ∪ B)) (min1 sA sB) := by
  rcases hInfA with ⟨h_sA_lower, h_sA_greatest⟩
  rcases hInfB with ⟨h_sB_lower, h_sB_greatest⟩
  constructor
  · intro x hx
    show LT.lt (if LT.lt sA sB then sA else sB) (Power.coord1 x) ∨
      Power.coord1 x = (if LT.lt sA sB then sA else sB)
    by_cases h : LT.lt sA sB
    · rw [if_pos h]
      cases hx with
      | inl hxA =>
        exact h_sA_lower x hxA
      | inr hxB =>
        have h2 := h_sB_lower x hxB
        cases h2 with
        | inl hlt2 => left; exact lt_trans h hlt2
        | inr heq2 => left; rw [heq2]; exact h
    · rw [if_neg h]
      cases hx with
      | inl hxA =>
        have h1 := h_sA_lower x hxA
        rcases lt_trichotomy sA sB with hlt | heq | hgt
        · contradiction
        · cases h1 with
          | inl hlt1 => left; rw [← heq]; exact hlt1
          | inr heq1 => right; rw [← heq]; exact heq1
        · cases h1 with
          | inl hlt1 => left; exact lt_trans hgt hlt1
          | inr heq1 => left; rw [heq1]; exact hgt
      | inr hxB =>
        exact h_sB_lower x hxB
  · intro b hb
    have hbA : IsLowerBound1 A b := fun x hx => hb x (Or.inl hx)
    have hbB : IsLowerBound1 B b := fun x hx => hb x (Or.inr hx)
    have hA_ge_b := h_sA_greatest b hbA
    have hB_ge_b := h_sB_greatest b hbB
    show LT.lt b (if LT.lt sA sB then sA else sB) ∨
      b = (if LT.lt sA sB then sA else sB)
    by_cases h : LT.lt sA sB
    · rw [if_pos h]
      exact hA_ge_b
    · rw [if_neg h]
      exact hB_ge_b

theorem infOpenIntervalAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a : R) (b : Endpoint R)
    (hNotEmpty : (openInterval (Endpoint.finite a) b).Nonempty) :
    IsInfimum1 (openInterval (Endpoint.finite a) b) a := by
  constructor
  · intro x hx
    have hx' : LT.lt a (Power.coord1 x) := hx.left
    exact Or.inl hx'
  · intro y hy
    rcases lt_trichotomy y a with hya | heq | hay
    · exact Or.inl hya
    · exact Or.inr heq
    · obtain ⟨x0, hx0left, hx0right⟩ := hNotEmpty
      have hm_gt_a : LT.lt a (min1 y (Power.coord1 x0)) := by
        show LT.lt a (if LT.lt y (Power.coord1 x0) then y else Power.coord1 x0)
        by_cases h : LT.lt y (Power.coord1 x0)
        · rw [if_pos h]
          exact hay
        · rw [if_neg h]
          have hl : LT.lt a (Power.coord1 x0) := hx0left
          exact hl
      obtain ⟨z, ha_lt_z, hz_lt_min⟩ := exists_between hm_gt_a
      have hz_lt_b : Endpoint.lt (Endpoint.finite z) b := by
        cases b with
        | posInf => exact trivial
        | finite val =>
          have hx0_le_b : LT.lt (Power.coord1 x0) val := hx0right
          by_cases h : LT.lt y (Power.coord1 x0)
          · have hmin : min1 y (Power.coord1 x0) = y := by
              show (if LT.lt y (Power.coord1 x0) then y else Power.coord1 x0) = y
              rw [if_pos h]
            rw [hmin] at hz_lt_min
            have hy_lt_b : LT.lt y val := lt_trans h hx0_le_b
            exact lt_trans hz_lt_min hy_lt_b
          · have hmin : min1 y (Power.coord1 x0) = Power.coord1 x0 := by
              show (if LT.lt y (Power.coord1 x0) then y else Power.coord1 x0)
                = Power.coord1 x0
              rw [if_neg h]
            rw [hmin] at hz_lt_min
            exact lt_trans hz_lt_min hx0_le_b
        | negInf => exact False.elim hx0right
      have hzmem : openInterval (Endpoint.finite a) b (fun _ => z) :=
        ⟨ha_lt_z, hz_lt_b⟩
      have hz_ge_y := hy (fun _ => z) hzmem
      have hz_gt_y : LT.lt z y := by
        by_cases h : LT.lt y (Power.coord1 x0)
        · have hmin : min1 y (Power.coord1 x0) = y := by
            show (if LT.lt y (Power.coord1 x0) then y else Power.coord1 x0) = y
            rw [if_pos h]
          rw [hmin] at hz_lt_min
          exact hz_lt_min
        · have hmin : min1 y (Power.coord1 x0) = Power.coord1 x0 := by
            show (if LT.lt y (Power.coord1 x0) then y else Power.coord1 x0)
              = Power.coord1 x0
            rw [if_neg h]
          rw [hmin] at hz_lt_min
          have x0_le_y : LT.lt (Power.coord1 x0) y ∨ Power.coord1 x0 = y := by
            rcases lt_trichotomy (Power.coord1 x0) y with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr h2
            · exact absurd h3 h
          cases x0_le_y with
          | inl hlt => exact lt_trans hz_lt_min hlt
          | inr heq =>
            have hm2 : LT.lt z (Power.coord1 x0) := hz_lt_min
            rw [heq] at hm2
            exact hm2
      cases hz_ge_y with
      | inl hlt =>
        exact False.elim (lt_irrefl y (lt_trans hlt hz_gt_y))
      | inr heq =>
        have heq' : z = y := heq
        rw [heq'] at hz_gt_y
        exact False.elim (lt_irrefl y hz_gt_y)

theorem infCompletenessAux {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1))
    (hDef : FiniteUnionOfPointsAndIntervals A)
    (hNotEmpty : A.Nonempty)
    (hBounded : BoundedBelow1 A) :
    ∃ s : R, IsInfimum1 A s := by
  have hCore : ∀ (A : Set (Power R 1)),
      FiniteUnionOfPointsAndIntervals A ->
      BoundedBelow1 A → (∀ x, ¬ A x) ∨ (∃ s : R, IsInfimum1 A s) := by
    intro A hDef
    induction hDef with
    | empty =>
      intro hBounded
      left
      intro x hx
      exact hx
    | point =>
      rename_i a
      intro hBounded
      right
      use a
      constructor
      · intro x hx
        right
        exact hx
      · intro b hb
        let x_a : Power R 1 := fun _ => a
        have hx_in_set : pointSet a x_a := by rfl
        have h1 := hb x_a hx_in_set
        cases h1 with
        | inl hlt => exact Or.inl hlt
        | inr heq => exact Or.inr heq.symm
    | interval =>
      rename_i a b
      cases a with
      | posInf =>
        intro _
        left
        intro x hx
        exact hx.left
      | finite val =>
        intro _
        by_cases hEmpty : (openInterval (Endpoint.finite val) b).Nonempty
        · right
          use val
          exact infOpenIntervalAux val b hEmpty
        · left
          intro x hx
          exact hEmpty ⟨x, hx⟩
      | negInf =>
        cases b with
        | posInf =>
          intro hBounded
          by_cases hEmpty : (openInterval (R := R) Endpoint.negInf Endpoint.posInf).Nonempty
          · obtain ⟨x0, -, -⟩ := hEmpty
            rcases hBounded with ⟨m0, hm0_lower⟩
            obtain ⟨y, hym⟩ := exists_lt (min1 m0 (Power.coord1 x0))
            have hy_lt_m0 : LT.lt y m0 := by
              by_cases h : LT.lt m0 (Power.coord1 x0)
              · have hmin : min1 m0 (Power.coord1 x0) = m0 := by
                  show (if LT.lt m0 (Power.coord1 x0) then m0 else Power.coord1 x0) = m0
                  rw [if_pos h]
                rw [hmin] at hym
                exact hym
              · have hmin : min1 m0 (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if LT.lt m0 (Power.coord1 x0) then m0 else Power.coord1 x0)
                    = Power.coord1 x0
                  rw [if_neg h]
                rw [hmin] at hym
                have x0_le_m0 : LT.lt (Power.coord1 x0) m0 ∨ Power.coord1 x0 = m0 := by
                  rcases lt_trichotomy (Power.coord1 x0) m0 with h1 | h2 | h3
                  · exact Or.inl h1
                  · exact Or.inr h2
                  · exact absurd h3 h
                cases x0_le_m0 with
                | inl hlt => exact lt_trans hym hlt
                | inr heq => rw [heq] at hym; exact hym
            have hz_lt_b : Endpoint.lt (Endpoint.finite y) Endpoint.posInf := trivial
            let y_pow : Power R 1 := fun _ => y
            have hy_in : openInterval Endpoint.negInf Endpoint.posInf y_pow :=
              ⟨trivial, hz_lt_b⟩
            have hy_ge_m0 := hm0_lower y_pow hy_in
            cases hy_ge_m0 with
            | inl hlt =>
              exact False.elim (lt_irrefl y (lt_trans hy_lt_m0 hlt))
            | inr heq =>
              have heq' : y = m0 := heq
              rw [heq'] at hy_lt_m0
              exact False.elim (lt_irrefl m0 hy_lt_m0)
          · left
            intro x hx
            exact hEmpty ⟨x, hx⟩
        | finite val =>
          intro hBounded
          by_cases hEmpty : (openInterval Endpoint.negInf (Endpoint.finite val)).Nonempty
          · obtain ⟨x0, hx0left, hx0right⟩ := hEmpty
            rcases hBounded with ⟨m0, hm0_lower⟩
            obtain ⟨y, hym⟩ := exists_lt (min1 m0 (Power.coord1 x0))
            have hy_lt_m0 : LT.lt y m0 := by
              by_cases h : LT.lt m0 (Power.coord1 x0)
              · have hmin : min1 m0 (Power.coord1 x0) = m0 := by
                  show (if LT.lt m0 (Power.coord1 x0) then m0 else Power.coord1 x0) = m0
                  rw [if_pos h]
                rw [hmin] at hym
                exact hym
              · have hmin : min1 m0 (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if LT.lt m0 (Power.coord1 x0) then m0 else Power.coord1 x0)
                    = Power.coord1 x0
                  rw [if_neg h]
                rw [hmin] at hym
                have x0_le_m0 : LT.lt (Power.coord1 x0) m0 ∨ Power.coord1 x0 = m0 := by
                  rcases lt_trichotomy (Power.coord1 x0) m0 with h1 | h2 | h3
                  · exact Or.inl h1
                  · exact Or.inr h2
                  · exact absurd h3 h
                cases x0_le_m0 with
                | inl hlt => exact lt_trans hym hlt
                | inr heq => rw [heq] at hym; exact hym
            have hx0_le_b : LT.lt (Power.coord1 x0) val := hx0right
            have hz_lt_b : Endpoint.lt (Endpoint.finite y) (Endpoint.finite val) := by
              by_cases h : LT.lt m0 (Power.coord1 x0)
              · have hmin : min1 m0 (Power.coord1 x0) = m0 := by
                  show (if LT.lt m0 (Power.coord1 x0) then m0 else Power.coord1 x0) = m0
                  rw [if_pos h]
                rw [hmin] at hym
                have hm0_lt_b : LT.lt m0 val := by
                  have hml : LT.lt m0 (Power.coord1 x0) := h
                  exact lt_trans hml hx0_le_b
                exact lt_trans hym hm0_lt_b
              · have hmin : min1 m0 (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if LT.lt m0 (Power.coord1 x0) then m0 else Power.coord1 x0)
                    = Power.coord1 x0
                  rw [if_neg h]
                rw [hmin] at hym
                exact lt_trans hym hx0_le_b
            let y_pow : Power R 1 := fun _ => y
            have hy_in : openInterval Endpoint.negInf (Endpoint.finite val) y_pow :=
              ⟨trivial, hz_lt_b⟩
            have hy_ge_m0 := hm0_lower y_pow hy_in
            cases hy_ge_m0 with
            | inl hlt =>
              exact False.elim (lt_irrefl y (lt_trans hy_lt_m0 hlt))
            | inr heq =>
              have heq' : y = m0 := heq
              rw [heq'] at hy_lt_m0
              exact False.elim (lt_irrefl m0 hy_lt_m0)
          · left
            intro x hx
            exact hEmpty ⟨x, hx⟩
        | negInf =>
          intro _
          left
          intro x hx
          exact hx.right
    | union =>
      rename_i A B hFA hFB ihA ihB
      intro hBounded
      have hBoundA : BoundedBelow1 A := by
        rcases hBounded with ⟨b0, hb0⟩
        exact ⟨b0, fun x hx => hb0 x (Or.inl hx)⟩
      have hBoundB : BoundedBelow1 B := by
        rcases hBounded with ⟨b0, hb0⟩
        exact ⟨b0, fun x hx => hb0 x (Or.inr hx)⟩
      have hResA := ihA hBoundA
      have hResB := ihB hBoundB
      cases hResA with
      | inl hEmptyA =>
        cases hResB with
        | inl hEmptyB =>
          left
          intro x hx
          cases hx with
          | inl hxA => exact hEmptyA x hxA
          | inr hxB => exact hEmptyB x hxB
        | inr hInfB =>
          right
          rcases hInfB with ⟨sB, hsB_lower, hsB_greatest⟩
          use sB
          constructor
          · intro x hx
            cases hx with
            | inl hxA => exact False.elim (hEmptyA x hxA)
            | inr hxB => exact hsB_lower x hxB
          · intro b hb
            have hbB : IsLowerBound1 B b := fun x hx => hb x (Or.inr hx)
            exact hsB_greatest b hbB
      | inr hInfA =>
        cases hResB with
        | inl hEmptyB =>
          right
          rcases hInfA with ⟨sA, hsA_lower, hsA_greatest⟩
          use sA
          constructor
          · intro x hx
            cases hx with
            | inl hxA => exact hsA_lower x hxA
            | inr hxB => exact False.elim (hEmptyB x hxB)
          · intro b hb
            have hbA : IsLowerBound1 A b := fun x hx => hb x (Or.inl hx)
            exact hsA_greatest b hbA
        | inr hInfB =>
          right
          rcases hInfA with ⟨sA, hsA⟩
          rcases hInfB with ⟨sB, hsB⟩
          use min1 sA sB
          exact infUnionAux A B sA sB hsA hsB
  cases hCore A hDef hBounded with
  | inl hEmpty =>
    rcases hNotEmpty with ⟨x, hx⟩
    exact False.elim (hEmpty x hx)
  | inr hInf =>
    exact hInf

-- Finite good partition: assembly from the three lemmas (see monotonicity.tex).
-- X-classes: points with a constant / increasing / decreasing window.
-- Bad = I' minus the classes is finite; endpoints of everything give the partition.
-- The Mathlib order/typeclass context makes a few heavy tactics need more heartbeats.
set_option maxHeartbeats 1000000 in
theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Power R 1} (hab : Lt1 a b)
    (hsubIJ : (openInterval (Endpoint.finite (Power.coord1 a)) (Endpoint.finite (Power.coord1 b))).Subset I) :
    ∃ k : Nat, ∃ p : Fin (k + 1) → Power R 1,
      p 0 = a ∧ p (Fin.last k) = b ∧
      (∀ i : Fin k, Lt1 (p i.castSucc) (p i.succ)) ∧
      (∀ i : Fin k,
        let J : Set (Power R 1) := openInterval (Endpoint.finite ((p i.castSucc) 0)) (Endpoint.finite ((p i.succ) 0))
        (((∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y ->
          f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI)) ∧
          J.Subset (ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun))) ∨
         (((∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y → Lt1 x y ->
            Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∨
           (∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y → Lt1 x y ->
            Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) ∧
          J.Subset (ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun))))) := by
  have hac : Power.coord1 a = Power.coord1 a := rfl
  set ac : R := Power.coord1 a with hacdef
  set bc : R := Power.coord1 b with hbcdef
  have habc : LT.lt ac bc := hab
  set J₀ : Set (Power R 1) := openInterval (Endpoint.finite ac) (Endpoint.finite bc) with hJdef
  have hJmem : M.S 1 J₀ :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  set I' : Set (Power R 1) := (J₀ ∩ I) with hIdef
  have hI'mem : M.S 1 I' := M.inter_mem hJmem f.domain_mem
  -- The three local-type classes.
  set C : Set (Power R 1) := fun x : Power R 1 => J₀ x ∧ I x ∧
    (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
        openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) with hCdef
  have hCmem : M.S 1 C := constClassDefinable M f ac bc
  set U : Set (Power R 1) := fun x : Power R 1 => J₀ x ∧ I x ∧
    (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
        openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
        LT.lt pc qc ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
          ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) with hUdef
  have hUmem : M.S 1 U := incClassDefinable M f ac bc
  set Dc : Set (Power R 1) := fun x : Power R 1 => J₀ x ∧ I x ∧
    (∃ u v : R, LT.lt u (Power.coord1 x) ∧ LT.lt (Power.coord1 x) v ∧
      ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
        openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
        openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
        LT.lt pc qc ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => pc) (fun _ => wpc)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => qc) (fun _ => wqc)) ∧
        (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
          ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) with hDdef
  have hDmem : M.S 1 Dc := decClassDefinable M f ac bc
  set Bad : Set (Power R 1) := I' ∩ (C ∪ (U ∪ Dc))ᶜ with hBaddef
  have hBadmem : M.S 1 Bad :=
    M.inter_mem hI'mem (M.compl_mem (M.union_mem hCmem (M.union_mem hUmem hDmem)))
  -- Bad is finite: an interval inside would yield a good window via Lemmas 1, 2.
  have hBadfin : Set.Finite Bad := by
    by_contra hne
    have hInf : Set.Infinite Bad := hne
    obtain ⟨c, d, hltAB, hsubAB⟩ :=
      Monotonicity_Theorem.infinite_definable_set_contains_interval2 M Bad hBadmem hInf
    have hBadne : Bad.Nonempty := by
      by_contra hne'
      have hempty : ∀ x, ¬ Bad x := fun x hx => hne' ⟨x, hx⟩
      have hfin : Set.Finite Bad := by
        apply Set.finite_empty.subset
        intro x hx
        exact False.elim (hempty x hx)
      exact hne hfin
    obtain ⟨q₀, hq₀⟩ := hBadne
    have hJne : (openInterval c d).Nonempty := nonemptyWinAux hltAB q₀
    obtain ⟨p, hp⟩ := hJne
    obtain ⟨u, v, huv, hsubUV⟩ := finiteSubwindowAux hp
    have hJ'sub : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x → Bad x :=
      fun x hx => hsubAB (hsubUV x hx)
    have hJ'I : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x → I x := by
      intro x hx
      have hBx : Bad x := hJ'sub x hx
      rw [hBaddef] at hBx
      obtain ⟨hI', -⟩ := hBx
      rw [hIdef] at hI'
      exact hI'.right
    have hJ'inf : Set.Infinite (openInterval (Endpoint.finite u) (Endpoint.finite v)) := by
      intro hfin
      have hfin' : Set.Finite (openInterval (Endpoint.finite u) (Endpoint.finite v)) := hfin
      set LC : List R := hfin'.toFinset.image Power.coord1 |>.toList with hLCdef
      have hLC : ∀ x : Power R 1, openInterval (Endpoint.finite u) (Endpoint.finite v) x →
          Power.coord1 x ∈ LC := by
        intro x hx
        rw [hLCdef]
        exact Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨x, hfin'.mem_toFinset.mpr hx, rfl⟩)
      exact intervalInfiniteAux LC u v huv hLC
    have hA'ne : ((openInterval (Endpoint.finite u) (Endpoint.finite v)) ∩ I).Nonempty := by
      obtain ⟨r, hr1, hr2⟩ := exists_between huv
      have hrB : Bad (fun _ => r) := hJ'sub _ ⟨hr1, hr2⟩
      rw [hBaddef] at hrB
      obtain ⟨hI', -⟩ := hrB
      exact ⟨fun _ => r, ⟨⟨hr1, hr2⟩, hJ'I _ ⟨hr1, hr2⟩⟩⟩
    obtain ⟨p₀, hp₀⟩ := hA'ne
    set A' : Set (Power R 1) :=
      (openInterval (Endpoint.finite u) (Endpoint.finite v)) ∩ I with hAdef
    have hA'mem : M.S 1 A' :=
      M.inter_mem ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)) f.domain_mem
    have hAsub : A'.Subset I := fun x hx => hx.right
    have hAJ' : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x → A' x :=
      fun x hx => ⟨hx, hJ'I x hx⟩
    have hI'A : Set.Infinite A' := by
      intro hfin
      apply hJ'inf
      have hfin' : Set.Finite A' := hfin
      exact hfin'.subset hAJ'
    obtain ⟨f', hagree⟩ := restrictDefinable f A' hA'mem hAsub
    obtain ⟨e1, e2, hlt12, hsub12, hconstOrInj⟩ :=
      Monotonicity_Theorem.lemma_one M f' hI'A
    have hWsub : ∀ x, openInterval e1 e2 x → Bad x := by
      intro x hx
      have hAx : A' x := hsub12 hx
      rw [hAdef] at hAx
      exact hJ'sub x hAx.left
    have hWne : (openInterval e1 e2).Nonempty := nonemptyWinAux hlt12 p₀
    obtain ⟨w₀, hw₀⟩ := hWne
    -- Every point of W is in I' with a finite const/inj window available.
    have hWJ₀ : ∀ x, openInterval e1 e2 x → J₀ x := by
      intro x hx
      have hBx : Bad x := hWsub x hx
      rw [hBaddef] at hBx
      obtain ⟨hI', -⟩ := hBx
      rw [hIdef] at hI'
      exact hI'.left
    have hWI : ∀ x, openInterval e1 e2 x → I x := by
      intro x hx
      have hBx : Bad x := hWsub x hx
      rw [hBaddef] at hBx
      obtain ⟨hI', -⟩ := hBx
      rw [hIdef] at hI'
      exact hI'.right
    rcases hconstOrInj with hconst | hinj
    · -- Constant on W: W ⊆ C, against W ⊆ Bad.
      have hWC : ∀ z, openInterval e1 e2 z → C z := by
        intro z hz
        obtain ⟨u₀, v₀, huz, hzv, hsubW⟩ := shrinkWindowAux hz
        refine ⟨hWJ₀ z hz, hWI z hz, u₀, v₀, huz, hzv, ?_⟩
        intro hex
        obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hGp, hGq, hne'⟩ := hex
        have hpW : openInterval e1 e2 (fun _ => pc) := hsubW _ hJp
        have hqW : openInterval e1 e2 (fun _ => qc) := hsubW _ hJq
        have hpA : A' (fun _ => pc) := hsub12 hpW
        have hqA : A' (fun _ => qc) := hsub12 hqW
        have hval : f'.toFun (Subtype.mk (fun _ => pc) hpA) =
            f'.toFun (Subtype.mk (fun _ => qc) hqA) :=
          hconst _ hpA hpW _ hqA hqW
        have hagp : f'.toFun (Subtype.mk (fun _ => pc) hpA) =
            f.toFun (Subtype.mk (fun _ => pc) (hAsub hpA)) := hagree _ hpA
        have hagq : f'.toFun (Subtype.mk (fun _ => qc) hqA) =
            f.toFun (Subtype.mk (fun _ => qc) (hAsub hqA)) := hagree _ hqA
        have hsubEq : (f.toFun (Subtype.mk (fun _ => pc) (hAsub hpA))) =
            (f.toFun (Subtype.mk (fun _ => qc) (hAsub hqA))) := by
          rw [← hagp, ← hagq]
          exact hval
        have hwp : wpc =
            Power.coord1 ((f.toFun (Subtype.mk (fun _ => pc) (hAsub hpA))).1) :=
          graphValAux f _ _ (hAsub hpA) hGp
        have hwq : wqc =
            Power.coord1 ((f.toFun (Subtype.mk (fun _ => qc) (hAsub hqA))).1) :=
          graphValAux f _ _ (hAsub hqA) hGq
        have hsubc : Power.coord1 ((f.toFun (Subtype.mk (fun _ => pc) (hAsub hpA))).1) =
            Power.coord1 ((f.toFun (Subtype.mk (fun _ => qc) (hAsub hqA))).1) := by
          rw [hsubEq]
        apply hne'
        funext i
        show wpc = wqc
        rw [hwp, hwq]
        exact hsubc
      have hcon : C w₀ ∧ Bad w₀ := ⟨hWC w₀ hw₀, hWsub w₀ hw₀⟩
      obtain ⟨hCw, hBw⟩ := hcon
      rw [hBaddef] at hBw
      obtain ⟨-, hNB⟩ := hBw
      exact hNB (Or.inl hCw)
    · -- Injective on W: shrink to finite window, apply Lemma 2, land in U or Dc.
      obtain ⟨u₀, v₀, hu₀, hv₀, hsubW₀⟩ := shrinkWindowAux hw₀
      have huv₀ : LT.lt u₀ v₀ := lt_trans hu₀ hv₀
      set J₁ : Set (Power R 1) := openInterval (Endpoint.finite u₀) (Endpoint.finite v₀) with hJ₁def
      have hJ₁W : ∀ x, J₁ x → openInterval e1 e2 x := fun x hx => hsubW₀ x hx
      have hJ₁A' : ∀ x, J₁ x → A' x := by
        intro x hx
        have hWx : openInterval e1 e2 x := hJ₁W x hx
        have hAx : A' x := hsub12 hWx
        exact hAx
      set A₁ : Set (Power R 1) := (J₁ ∩ A') with hA₁def
      have hA₁mem : M.S 1 A₁ :=
        M.inter_mem ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)) hA'mem
      have hA₁sub : A₁.Subset A' := fun x hx => hx.right
      have hA₁J : ∀ x, A₁ x → J₁ x := fun x hx => hx.left
      have hI₁ : Set.Infinite A₁ := by
        intro hfin
        have hfin' : Set.Finite A₁ := hfin
        set LC : List R := hfin'.toFinset.image Power.coord1 |>.toList with hLCdef
        have hLC : ∀ x : Power R 1, J₁ x → Power.coord1 x ∈ LC := by
          intro x hx
          rw [hLCdef]
          exact Finset.mem_toList.mpr
            (Finset.mem_image.mpr ⟨x, hfin'.mem_toFinset.mpr ⟨hx, hJ₁A' x hx⟩, rfl⟩)
        exact intervalInfiniteAux LC u₀ v₀ huv₀ hLC
      obtain ⟨f₁, hagree₁⟩ := restrictDefinable f' A₁ hA₁mem hA₁sub
      have hinj₁ : ∀ x y (hx : A₁ x) (hy : A₁ y),
          f₁.toFun (Subtype.mk x hx) = f₁.toFun (Subtype.mk y hy) → x = y := by
        intro x y hx hy hval
        have hval' : f'.toFun (Subtype.mk x (hA₁sub hx)) =
            f'.toFun (Subtype.mk y (hA₁sub hy)) := by
          have e1 := hagree₁ x hx
          have e2 := hagree₁ y hy
          rw [e1, e2] at hval
          exact hval
        exact hinj _ (hA₁sub hx) (hsubW₀ x (hA₁J x hx)) _ (hA₁sub hy)
          (hsubW₀ y (hA₁J y hy)) hval'
      obtain ⟨a2, b2, hlt2, hsub2, hor⟩ :=
        Monotonicity_Theorem.lemma_two M f₁ hI₁ hinj₁
      have hW'ne : (openInterval a2 b2).Nonempty := nonemptyWinAux hlt2 p₀
      obtain ⟨w₁, hw₁⟩ := hW'ne
      have hW'Bad : ∀ x, openInterval a2 b2 x → Bad x := by
        intro x hx
        have hAx : A' x := hA₁sub (hsub2 x hx)
        rw [hAdef] at hAx
        exact hJ'sub x hAx.left
      have hW'J₀ : ∀ x, openInterval a2 b2 x → J₀ x := by
        intro x hx
        have hBx : Bad x := hW'Bad x hx
        rw [hBaddef] at hBx
        obtain ⟨hI', -⟩ := hBx
        rw [hIdef] at hI'
        exact hI'.left
      have hW'I : ∀ x, openInterval a2 b2 x → I x := by
        intro x hx
        have hBx : Bad x := hW'Bad x hx
        rw [hBaddef] at hBx
        obtain ⟨hI', -⟩ := hBx
        rw [hIdef] at hI'
        exact hI'.right
      rcases hor with hinc | hdec
      · -- Increasing window: W' ⊆ U.
        have hW'U : ∀ z, openInterval a2 b2 z → U z := by
          intro z hz
          obtain ⟨s, t, hsz, hzt, hsubW'⟩ := shrinkWindowAux hz
          refine ⟨hW'J₀ z hz, hW'I z hz, s, t, hsz, hzt, ?_⟩
          intro hex
          obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hPq, hGp, hGq, hBAD⟩ := hex
          have hpW' : openInterval a2 b2 (fun _ => pc) := hsubW' _ hJp
          have hqW' : openInterval a2 b2 (fun _ => qc) := hsubW' _ hJq
          have hpA : A₁ (fun _ => pc) := hsub2 _ hpW'
          have hqA : A₁ (fun _ => qc) := hsub2 _ hqW'
          have hPQ : Lt1 (fun _ => pc) (fun _ => qc) := hPq
          have hval : Lt1 (f₁.toFun (Subtype.mk (fun _ => pc) hpA)).1
              (f₁.toFun (Subtype.mk (fun _ => qc) hqA)).1 :=
            hinc _ hpA _ hqA hpW' hqW' hPQ
          have hagp : f₁.toFun (Subtype.mk (fun _ => pc) hpA) =
              f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA))) := by
            have e1 : f₁.toFun (Subtype.mk (fun _ => pc) hpA) =
                f'.toFun (Subtype.mk (fun _ => pc) (hA₁sub hpA)) := hagree₁ _ hpA
            have e2 : f'.toFun (Subtype.mk (fun _ => pc) (hA₁sub hpA)) =
                f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA))) := hagree _ (hA₁sub hpA)
            rw [e1, e2]
          have hagq : f₁.toFun (Subtype.mk (fun _ => qc) hqA) =
              f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA))) := by
            have e1 : f₁.toFun (Subtype.mk (fun _ => qc) hqA) =
                f'.toFun (Subtype.mk (fun _ => qc) (hA₁sub hqA)) := hagree₁ _ hqA
            have e2 : f'.toFun (Subtype.mk (fun _ => qc) (hA₁sub hqA)) =
                f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA))) := hagree _ (hA₁sub hqA)
            rw [e1, e2]
          have hwp : wpc =
              Power.coord1 ((f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA)))).1) :=
            graphValAux f _ _ (hAsub (hA₁sub hpA)) hGp
          have hwq : wqc =
              Power.coord1 ((f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA)))).1) :=
            graphValAux f _ _ (hAsub (hA₁sub hqA)) hGq
          have hlt : LT.lt wpc wqc := by
            have e1 : Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => pc) hpA)).1) =
                Power.coord1 ((f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA)))).1) := by
              rw [hagp]
            have e2 : Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => qc) hqA)).1) =
                Power.coord1 ((f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA)))).1) := by
              rw [hagq]
            have hval' : LT.lt (Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => pc) hpA)).1))
                (Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => qc) hqA)).1)) := hval
            rw [e1, e2, ← hwp, ← hwq] at hval'
            exact hval'
          rcases hBAD with hBADlt | hBADeq
          · have hlt2' : LT.lt wqc wpc := hBADlt
            exact lt_irrefl _ (lt_trans hlt hlt2')
          · have heq' : wpc = wqc := by
              have : ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)) := hBADeq
              exact congrFun this ⟨0, by decide⟩
            rw [heq'] at hlt
            exact lt_irrefl _ hlt
        have hcon : U w₁ ∧ Bad w₁ := ⟨hW'U w₁ hw₁, hW'Bad w₁ hw₁⟩
        obtain ⟨hUw, hBw⟩ := hcon
        rw [hBaddef] at hBw
        obtain ⟨-, hNB⟩ := hBw
        exact hNB (Or.inr (Or.inl hUw))
      · -- Decreasing window: W' ⊆ Dc.
        have hW'D : ∀ z, openInterval a2 b2 z → Dc z := by
          intro z hz
          obtain ⟨s, t, hsz, hzt, hsubW'⟩ := shrinkWindowAux hz
          refine ⟨hW'J₀ z hz, hW'I z hz, s, t, hsz, hzt, ?_⟩
          intro hex
          obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq, hPq, hGp, hGq, hBAD⟩ := hex
          have hpW' : openInterval a2 b2 (fun _ => pc) := hsubW' _ hJp
          have hqW' : openInterval a2 b2 (fun _ => qc) := hsubW' _ hJq
          have hpA : A₁ (fun _ => pc) := hsub2 _ hpW'
          have hqA : A₁ (fun _ => qc) := hsub2 _ hqW'
          have hPQ : Lt1 (fun _ => pc) (fun _ => qc) := hPq
          have hval : Lt1 (f₁.toFun (Subtype.mk (fun _ => qc) hqA)).1
              (f₁.toFun (Subtype.mk (fun _ => pc) hpA)).1 :=
            hdec _ hpA _ hqA hpW' hqW' hPQ
          have hagp : f₁.toFun (Subtype.mk (fun _ => pc) hpA) =
              f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA))) := by
            have e1 : f₁.toFun (Subtype.mk (fun _ => pc) hpA) =
                f'.toFun (Subtype.mk (fun _ => pc) (hA₁sub hpA)) := hagree₁ _ hpA
            have e2 : f'.toFun (Subtype.mk (fun _ => pc) (hA₁sub hpA)) =
                f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA))) := hagree _ (hA₁sub hpA)
            rw [e1, e2]
          have hagq : f₁.toFun (Subtype.mk (fun _ => qc) hqA) =
              f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA))) := by
            have e1 : f₁.toFun (Subtype.mk (fun _ => qc) hqA) =
                f'.toFun (Subtype.mk (fun _ => qc) (hA₁sub hqA)) := hagree₁ _ hqA
            have e2 : f'.toFun (Subtype.mk (fun _ => qc) (hA₁sub hqA)) =
                f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA))) := hagree _ (hA₁sub hqA)
            rw [e1, e2]
          have hwp : wpc =
              Power.coord1 ((f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA)))).1) :=
            graphValAux f _ _ (hAsub (hA₁sub hpA)) hGp
          have hwq : wqc =
              Power.coord1 ((f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA)))).1) :=
            graphValAux f _ _ (hAsub (hA₁sub hqA)) hGq
          have hlt : LT.lt wqc wpc := by
            have e1 : Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => qc) hqA)).1) =
                Power.coord1 ((f.toFun (Subtype.mk (fun _ => qc) (hAsub (hA₁sub hqA)))).1) := by
              rw [hagq]
            have e2 : Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => pc) hpA)).1) =
                Power.coord1 ((f.toFun (Subtype.mk (fun _ => pc) (hAsub (hA₁sub hpA)))).1) := by
              rw [hagp]
            have hval' : LT.lt (Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => qc) hqA)).1))
                (Power.coord1 ((f₁.toFun (Subtype.mk (fun _ => pc) hpA)).1)) := hval
            rw [e1, e2, ← hwq, ← hwp] at hval'
            exact hval'
          rcases hBAD with hBADlt | hBADeq
          · have hlt2' : LT.lt wpc wqc := hBADlt
            exact lt_irrefl _ (lt_trans hlt hlt2')
          · have heq' : wpc = wqc := by
              have : ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)) := hBADeq
              exact congrFun this ⟨0, by decide⟩
            rw [heq'] at hlt
            exact lt_irrefl _ hlt
        have hcon : Dc w₁ ∧ Bad w₁ := ⟨hW'D w₁ hw₁, hW'Bad w₁ hw₁⟩
        obtain ⟨hDw, hBw⟩ := hcon
        rw [hBaddef] at hBw
        obtain ⟨-, hNB⟩ := hBw
        exact hNB (Or.inr (Or.inr hDw))
  -- Endpoint collection and sorting.
  have hBadFin : Set.Finite Bad := hBadfin
  set BadList : List R := hBadFin.toFinset.image Power.coord1 |>.toList with hBadListdef
  have hBadListMp : ∀ x : Power R 1, Bad x → Power.coord1 x ∈ BadList := by
    intro x hx
    rw [hBadListdef]
    exact Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨x, hBadFin.mem_toFinset.mpr hx, rfl⟩)
  have hDiscfin : Set.Finite (fun p : Power R 1 => ∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
      (Power.append p t)) :=
    disc_finite_aux M f
  set DiscList : List R := hDiscfin.toFinset.image Power.coord1 |>.toList with hDiscListdef
  have hDiscListMp : ∀ x : Power R 1, (∃ t : Power R 3,
      (fun x4 : Power R 4 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => x4 (dGx4 j)) ∧
      LT.lt ((fun j : Fin 2 => x4 (dE1w4 j)) 0) ((fun j : Fin 2 => x4 (dE1w4 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x4 (dWe24 j)) 0) ((fun j : Fin 2 => x4 (dWe24 j)) 1) ∧
      (¬ ∃ t2 : Power R 2,
      (fun x6 : Power R 6 =>
      LT.lt ((fun j : Fin 2 => x6 (dD1x6 j)) 0) ((fun j : Fin 2 => x6 (dD1x6 j)) 1) ∧
      LT.lt ((fun j : Fin 2 => x6 (dXD26 j)) 0) ((fun j : Fin 2 => x6 (dXD26 j)) 1) ∧
      (¬ ∃ t3 : Power R 2,
      (fun q : Power R 8 =>
      I (fun i : Fin 1 => q (dIx i)) ∧
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (dGy j)) ∧
      LT.lt ((fun j : Fin 2 => q (dD1y j)) 0) ((fun j : Fin 2 => q (dD1y j)) 1) ∧
      LT.lt ((fun j : Fin 2 => q (dYD2 j)) 0) ((fun j : Fin 2 => q (dYD2 j)) 1) ∧
      ¬ (LT.lt ((fun j : Fin 2 => q (dE1q j)) 0) ((fun j : Fin 2 => q (dE1q j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (dQe2 j)) 0) ((fun j : Fin 2 => q (dQe2 j)) 1)))
        (Power.append x6 t3)))
        (Power.append x4 t2)))
      (Power.append x t)) → Power.coord1 x ∈ DiscList := by
    intro x hx
    rw [hDiscListdef]
    exact Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨x, hDiscfin.mem_toFinset.mpr hx, rfl⟩)
  obtain ⟨LI', hLI'⟩ := atomicExists I' ((M.ominimal _).mp hI'mem)
  obtain ⟨LC, hLC⟩ := atomicExists C ((M.ominimal _).mp hCmem)
  obtain ⟨LU, hLU⟩ := atomicExists U ((M.ominimal _).mp hUmem)
  obtain ⟨LDc, hLDc⟩ := atomicExists Dc ((M.ominimal _).mp hDmem)
  set E : List R := ac :: bc :: BadList ++ DiscList ++ LI' ++ LC ++ LU ++ LDc with hEdef
  set Srt : List R := sortList E with hSrtdef
  have hSrtSorted : SortedLT Srt := sortList_sorted E
  have hSrtmem : ∀c, c ∈ Srt ↔ c ∈ E := sortList_mem E
  have hacS : ac ∈ Srt := (hSrtmem ac).mpr (List.mem_cons.mpr (Or.inl rfl))
  have hbcS : bc ∈ Srt := (hSrtmem bc).mpr
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  obtain ⟨ia, hia⟩ := memGetAux Srt ac hacS
  obtain ⟨ib, hib⟩ := memGetAux Srt bc hbcS
  have hiab : ia.val < ib.val := by
    rcases Nat.lt_or_ge ia.val ib.val with h | h
    · exact h
    · exfalso
      by_cases heq : ib.val = ia.val
      · have e : ib = ia := Fin.ext heq
        have : ac = bc := by rw [← hia, ← hib, e]
        rw [this] at habc
        exact lt_irrefl _ habc
      · have hlt : ib.val < ia.val := by omega
        have hlt2 : LT.lt bc ac := by
          rw [← hib, ← hia]
          exact sortedGetLT Srt hSrtSorted ib ia hlt
        exact lt_irrefl _ (lt_trans hlt2 habc)
  -- Cut points from ia to ib.
  set k : Nat := ib.val - ia.val with hkdef
  have hklen : ia.val + k = ib.val := by omega
  have hbound : ∀ t : Fin (k + 1), ia.val + t.val < Srt.length := by
    intro t
    have ht : t.val < k + 1 := t.isLt
    have hibL : ib.val < Srt.length := ib.isLt
    omega
  set p : Fin (k + 1) → Power R 1 := fun t => fun _ => Srt.get ⟨ia.val + t.val, hbound t⟩ with hpdef
  have hp0 : p 0 = a := by
    have h0 : ((0 : Fin (k + 1))).val = 0 := rfl
    have e : (⟨ia.val + (0 : Fin (k + 1)).val, hbound 0⟩ : Fin Srt.length) = ia := by
      apply Fin.ext
      show ia.val + (0 : Fin (k + 1)).val = ia.val
      rw [h0, Nat.add_zero]
    show (fun _ : Fin 1 => Srt.get ⟨ia.val + (0 : Fin (k + 1)).val, hbound 0⟩) = a
    rw [e, hia]
    exact ptEqAux rfl
  have hplast : p (Fin.last k) = b := by
    have hL : ((Fin.last k)).val = k := rfl
    have e : (⟨ia.val + (Fin.last k).val, hbound (Fin.last k)⟩ : Fin Srt.length) = ib := by
      apply Fin.ext
      show ia.val + (Fin.last k).val = ib.val
      rw [hL]
      omega
    show (fun _ : Fin 1 => Srt.get ⟨ia.val + (Fin.last k).val, hbound (Fin.last k)⟩) = b
    rw [e, hib]
    exact ptEqAux rfl
  refine ⟨k, p, hp0, hplast, ?_, ?_⟩
  · -- Consecutive cut points strictly increase.
    intro i
    have hi1 : (i.castSucc).val = i.val := rfl
    have hi2 : (i.succ).val = i.val + 1 := rfl
    have hb1 : ia.val + i.val + 1 < Srt.length := by
      have ht : i.val < k + 1 := by
        have := i.isLt
        omega
      have hibL : ib.val < Srt.length := ib.isLt
      omega
    show LT.lt (Srt.get ⟨ia.val + i.val, by omega⟩) (Srt.get ⟨ia.val + i.val + 1, by omega⟩)
    exact sortedStepAux Srt hSrtSorted (ia.val + i.val) hb1
  · -- Each piece is good.
    intro i
    set lo : R := ((p i.castSucc) 0) with hlodef
    set hi : R := ((p i.succ) 0) with hhidef
    have hlohi : LT.lt lo hi := by
      have hi1 : (i.castSucc).val = i.val := rfl
      have hi2 : (i.succ).val = i.val + 1 := rfl
      have hb1 : ia.val + i.val + 1 < Srt.length := by
        have ht : i.val < k + 1 := by
          have := i.isLt
          omega
        have hibL : ib.val < Srt.length := ib.isLt
        omega
      show LT.lt (Srt.get ⟨ia.val + i.val, by omega⟩) (Srt.get ⟨ia.val + i.val + 1, by omega⟩)
      exact sortedStepAux Srt hSrtSorted (ia.val + i.val) hb1
    have eLo : lo = Srt.get ⟨ia.val + i.val, by
        have ht : i.val < k + 1 := by
          have := i.isLt
          omega
        have hibL : ib.val < Srt.length := ib.isLt
        omega⟩ := rfl
    have eHi : hi = Srt.get ⟨ia.val + i.val + 1, by
        have ht : i.val < k + 1 := by
          have := i.isLt
          omega
        have hibL : ib.val < Srt.length := ib.isLt
        omega⟩ := rfl
    have hconsec : ∀ e ∈ E, ¬ (LT.lt lo e ∧ LT.lt e hi) := by
      intro e he hcon
      obtain ⟨hlo_e, he_hi⟩ := hcon
      have heS : e ∈ Srt := (hSrtmem e).mpr he
      obtain ⟨j, hj⟩ := memGetAux Srt e heS
      rcases Nat.lt_or_ge j.val (ia.val + i.val) with h | h
      · have hlt : LT.lt e lo := by
          rw [eLo, ← hj]
          exact sortedGetLT Srt hSrtSorted j ⟨ia.val + i.val, by
            have ht : i.val < k + 1 := by
              have := i.isLt
              omega
            have hibL : ib.val < Srt.length := ib.isLt
            omega⟩ h
        exact lt_irrefl _ (lt_trans hlt hlo_e)
      · rcases Nat.lt_or_ge (ia.val + i.val + 1) j.val with h2 | h2
        · have hlt : LT.lt hi e := by
            rw [eHi, ← hj]
            exact sortedGetLT Srt hSrtSorted ⟨ia.val + i.val + 1, by
              have ht : i.val < k + 1 := by
                have := i.isLt
                omega
              have hibL : ib.val < Srt.length := ib.isLt
              omega⟩ j h2
          exact lt_irrefl _ (lt_trans he_hi hlt)
        · have h2eq : j.val = ia.val + i.val ∨ j.val = ia.val + i.val + 1 := by omega
          rcases h2eq with heq | heq
          · have e2 : (⟨ia.val + i.val, by
                have ht : i.val < k + 1 := by
                  have := i.isLt
                  omega
                have hibL : ib.val < Srt.length := ib.isLt
                omega⟩ : Fin Srt.length) = j := Fin.ext heq.symm
            have : e = lo := by rw [← hj, ← e2, eLo]
            rw [this] at hlo_e
            exact lt_irrefl _ hlo_e
          · have e2 : (⟨ia.val + i.val + 1, by
                have ht : i.val < k + 1 := by
                  have := i.isLt
                  omega
                have hibL : ib.val < Srt.length := ib.isLt
                omega⟩ : Fin Srt.length) = j := Fin.ext heq.symm
            have : e = hi := by rw [← hj, ← e2, eHi]
            rw [this] at he_hi
            exact lt_irrefl _ he_hi
    -- Atomic endpoints all lie in E.
    have hLI'E : ∀ c ∈ LI', c ∈ E := by
      intro c hc
      show c ∈ (ac :: bc :: BadList ++ DiscList ++ LI' ++ LC ++ LU ++ LDc)
      simp only [List.mem_cons, List.mem_append]
      tauto
    have hLC'E : ∀ c ∈ LC, c ∈ E := by
      intro c hc
      show c ∈ (ac :: bc :: BadList ++ DiscList ++ LI' ++ LC ++ LU ++ LDc)
      simp only [List.mem_cons, List.mem_append]
      tauto
    have hLU'E : ∀ c ∈ LU, c ∈ E := by
      intro c hc
      show c ∈ (ac :: bc :: BadList ++ DiscList ++ LI' ++ LC ++ LU ++ LDc)
      simp only [List.mem_cons, List.mem_append]
      tauto
    have hLD'E : ∀ c ∈ LDc, c ∈ E := by
      intro c hc
      show c ∈ (ac :: bc :: BadList ++ DiscList ++ LI' ++ LC ++ LU ++ LDc)
      simp only [List.mem_cons, List.mem_append]
      tauto
    have hBad'E : ∀ c ∈ BadList, c ∈ E := by
      intro c hc
      show c ∈ (ac :: bc :: BadList ++ DiscList ++ LI' ++ LC ++ LU ++ LDc)
      simp only [List.mem_cons, List.mem_append]
      tauto
    have hDisc'E : ∀ c ∈ DiscList, c ∈ E := by
      intro c hc
      show c ∈ (ac :: bc :: BadList ++ DiscList ++ LI' ++ LC ++ LU ++ LDc)
      simp only [List.mem_cons, List.mem_append]
      tauto
    -- The piece lies in J₀.
    have hlo_ac : lo = ac ∨ LT.lt ac lo := by
      by_cases h0 : i.val = 0
      · left
        have heq' : ia.val + i.val = ia.val := by omega
        rw [eLo]
        exact (congrArg Srt.get (Fin.ext heq')).trans hia
      · right
        have hlt : ia.val < ia.val + i.val := by omega
        rw [eLo, ← hia]
        exact sortedGetLT Srt hSrtSorted ⟨ia.val, ia.isLt⟩
          ⟨ia.val + i.val, by
            have ht : i.val < k + 1 := by
              have := i.isLt
              omega
            have hibL : ib.val < Srt.length := ib.isLt
            omega⟩ hlt
    have hhi_bc : hi = bc ∨ LT.lt hi bc := by
      by_cases h0 : i.val + 1 = k
      · left
        have heq' : ia.val + i.val + 1 = ib.val := by omega
        rw [eHi]
        exact (congrArg Srt.get (Fin.ext heq')).trans hib
      · right
        have hlt : ia.val + i.val + 1 < ib.val := by omega
        rw [eHi, ← hib]
        exact sortedGetLT Srt hSrtSorted
          ⟨ia.val + i.val + 1, by
            have ht : i.val < k + 1 := by
              have := i.isLt
              omega
            have hibL : ib.val < Srt.length := ib.isLt
            omega⟩ ib hlt
    have hJsub : ∀ x : Power R 1, openInterval (Endpoint.finite lo) (Endpoint.finite hi) x →
        J₀ x := by
      intro x hJx
      obtain ⟨hlo_x, hx_hi⟩ := hJx
      show Endpoint.lt (Endpoint.finite ac) (Endpoint.finite (Power.coord1 x)) ∧
        Endpoint.lt (Endpoint.finite (Power.coord1 x)) (Endpoint.finite bc)
      rcases hlo_ac with heq | hlt
      · rcases hhi_bc with heq2 | hlt2
        · rw [← heq, ← heq2]
          exact ⟨hlo_x, hx_hi⟩
        · rw [← heq]
          exact ⟨hlo_x, lt_trans hx_hi hlt2⟩
      · rcases hhi_bc with heq2 | hlt2
        · rw [← heq2]
          exact ⟨lt_trans hlt hlo_x, hx_hi⟩
        · exact ⟨lt_trans hlt hlo_x, lt_trans hx_hi hlt2⟩
    -- Piece dichotomies.
    rcases hLI' E hLI'E lo hi hconsec with hIdis | hIcon
    · -- I' disjoint: impossible via domain hyp (J₀ ⊆ I, J ⊆ J₀, J nonempty).
      exfalso
      obtain ⟨m, hm_lo, hm_hi⟩ := exists_between hlohi
      have hJm : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => m) :=
        ⟨hm_lo, hm_hi⟩
      have hJ₀m : J₀ (fun _ => m) := hJsub _ hJm
      have hIm : I (fun _ => m) := hsubIJ hJ₀m
      exact hIdis _ hJm ⟨hJ₀m, hIm⟩
    · -- The piece lies in I'. No Bad point strictly inside.
      have hNB : ∀ x : Power R 1, openInterval (Endpoint.finite lo) (Endpoint.finite hi) x →
          ¬ Bad x := by
        intro x hJx hBx
        have hmem : Power.coord1 x ∈ BadList := hBadListMp x hBx
        have hE : Power.coord1 x ∈ E := hBad'E _ hmem
        exact hconsec _ hE ⟨hJx.left, hJx.right⟩
      rcases hLC E hLC'E lo hi hconsec with hCdis | hCcon
      · rcases hLU E hLU'E lo hi hconsec with hUdis | hUcon
        · rcases hLDc E hLD'E lo hi hconsec with hDdis | hDcon
          · -- No flavor anywhere: every point would be Bad. Impossible.
            obtain ⟨m, hm_lo, hm_hi⟩ := exists_between hlohi
            have hJm : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => m) :=
              ⟨hm_lo, hm_hi⟩
            have hIm : I' (fun _ => m) := hIcon _ hJm
            have hBm : Bad (fun _ => m) := by
              rw [hBaddef]
              refine ⟨hIm, ?_⟩
              intro hcon
              rcases hcon with hC | hU | hD
              · exact hCdis _ hJm hC
              · exact hUdis _ hJm hU
              · exact hDdis _ hJm hD
            exact False.elim (hNB _ hJm hBm)
          · -- Case Dc: decreasing covers the piece.
            obtain ⟨m, hm_lo, hm_hi⟩ := exists_between hlohi
            set xm : Power R 1 := fun _ => m with hxmdef
            have hJm : openInterval (Endpoint.finite lo) (Endpoint.finite hi) xm :=
              ⟨hm_lo, hm_hi⟩
            obtain ⟨hJ₀m, hImm, u₀, v₀, hu₀, hv₀, hNBd₀⟩ := hDcon xm hJm
            have hmu₀ : LT.lt u₀ m := hu₀
            have hmv₀ : LT.lt m v₀ := hv₀
            -- Decreasing from a Dc-violation-free window (general).
            have hEqWinDG : ∀ u v : R,
                (¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
                  openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
                  openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
                  LT.lt pc qc ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => pc) (fun _ => wpc)) ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => qc) (fun _ => wqc)) ∧
                  (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
                    ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) →
                ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                LT.lt u a → LT.lt a v → LT.lt u b → LT.lt b v → LT.lt a b →
                Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
              intro u v hNBw a b ha hb hau hav hbu hbv hab
              rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                  ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
              · have hlt := h
                exfalso
                apply hNBw
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
                exact hlt
              · have heq := h
                exfalso
                apply hNBw
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
                exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
              · have hlt := h
                exact hlt
            -- Increasing from a U-violation-free window (general, for later use).
            have hEqWinUGD : ∀ u v : R,
                (¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
                  openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
                  openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
                  LT.lt pc qc ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => pc) (fun _ => wpc)) ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => qc) (fun _ => wqc)) ∧
                  (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
                    ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) →
                ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                LT.lt u a → LT.lt a v → LT.lt u b → LT.lt b v → LT.lt a b →
                Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
              intro u v hNBw a b ha hb hau hav hbu hbv hab
              rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                  ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
              · have hlt := h
                exact hlt
              · have heq := h
                exfalso
                apply hNBw
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
                exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
              · have hlt := h
                exfalso
                apply hNBw
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
                exact hlt
            -- Equality from a const-violation-free window (general, for later use).
            have hEqCUD : ∀ u v : R,
                (¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
                  openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
                  openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => pc) (fun _ => wpc)) ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => qc) (fun _ => wqc)) ∧
                  ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) →
                ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                LT.lt u a → LT.lt a v → LT.lt u b → LT.lt b v →
                (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
              intro u v hNBw a b ha hb hau hav hbu hbv
              by_contra hne
              apply hNBw
              refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                (f.toFun ⟨fun _ => b, hb⟩).1 0,
                ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩,
                graphAppendConst f a ha, graphAppendConst f b hb, ?_⟩
              intro heq
              apply hne
              have h0 : (f.toFun ⟨fun _ => a, ha⟩).1 0 =
                  (f.toFun ⟨fun _ => b, hb⟩).1 0 :=
                congrFun heq ⟨0, by decide⟩
              have e1 : (f.toFun ⟨fun _ => a, ha⟩).1 =
                  (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0) := by
                funext k
                have hk : k.val = 0 := by
                  have := k.isLt
                  omega
                have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
                rw [ek]
                rfl
              have e2 : (f.toFun ⟨fun _ => b, hb⟩).1 =
                  (fun _ : Fin 1 => (f.toFun ⟨fun _ => b, hb⟩).1 0) := by
                funext k
                have hk : k.val = 0 := by
                  have := k.isLt
                  omega
                have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
                rw [ek]
                rfl
              rw [e1, e2, h0]
            -- Right decreasing-prefix set at m.
            set SD : Set (Power R 1) := fun c : Power R 1 =>
              openInterval (Endpoint.finite ac) (Endpoint.finite bc) c ∧
              LT.lt m (Power.coord1 c) ∧
              ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
                openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => pc) ∧
                openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => qc) ∧
                LT.lt m pc ∧ LT.lt pc (Power.coord1 c) ∧
                LT.lt m qc ∧ LT.lt qc (Power.coord1 c) ∧
                LT.lt pc qc ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => pc) (fun _ => wpc)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => qc) (fun _ => wqc)) ∧
                (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
                  ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) with hSDdef
            have hSDmem : M.S 1 SD := decPrefixRDefinable M f ac bc m
            -- Decreasing on a decreasing-prefix segment.
            have hEqSD : ∀ t : R, SD (fun _ => t) → ∀ a b : R,
                ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                LT.lt m a → LT.lt a t → LT.lt m b → LT.lt b t → LT.lt a b →
                Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
              intro t hT a b ha hb hma hat hmb hbt hab
              obtain ⟨hJt, hmt, hNV⟩ := hT
              have hta : LT.lt t bc := hJt.right
              have hac_a : LT.lt ac a := by
                rcases hlo_ac with heq | hlt
                · rw [← heq]
                  exact lt_trans hm_lo hma
                · exact lt_trans hlt (lt_trans hm_lo hma)
              have hac_b : LT.lt ac b := by
                rcases hlo_ac with heq | hlt
                · rw [← heq]
                  exact lt_trans hm_lo hmb
                · exact lt_trans hlt (lt_trans hm_lo hmb)
              rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                  ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
              · have hlt := h
                exfalso
                apply hNV
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hac_a, lt_trans hat hta⟩, ⟨hac_b, lt_trans hbt hta⟩,
                  hma, hat, hmb, hbt, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
                exact hlt
              · have heq := h
                exfalso
                apply hNV
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hac_a, lt_trans hat hta⟩, ⟨hac_b, lt_trans hbt hta⟩,
                  hma, hat, hmb, hbt, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
                exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
              · have hlt := h
                exact hlt
            have hmin2D : ∀ p q : R, LT.lt m p → LT.lt m q →
                ∃ t, LT.lt m t ∧ LT.lt t p ∧ LT.lt t q := by
              intro p q hmp hmq
              rcases lt_trichotomy p q with h | h | h
              · have hlt := h
                obtain ⟨t, hmt, htp⟩ := exists_between hmp
                exact ⟨t, hmt, htp, lt_trans htp hlt⟩
              · have heq := h
                obtain ⟨t, hmt, htp⟩ := exists_between hmp
                rw [heq] at htp ⊢
                exact ⟨t, hmt, htp, htp⟩
              · have hlt := h
                obtain ⟨t, hmt, htq⟩ := exists_between hmq
                exact ⟨t, hmt, lt_trans htq hlt, htq⟩
            set SD' : Set (Power R 1) := SD ∩
              (openInterval (Endpoint.finite m) (Endpoint.finite hi)) with hSD'def
            have hSD'mem : M.S 1 SD' :=
              M.inter_mem hSDmem
                ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _))
            have hSD'ne : SD'.Nonempty := by
              obtain ⟨t₁, hm1, h1v, h1h⟩ := hmin2D v₀ hi hmv₀ hm_hi
              obtain ⟨t, hmt, ht1, hbc⟩ := hmin2D t₁ bc hm1 hJ₀m.right
              have htv₀ : LT.lt t v₀ := lt_trans ht1 h1v
              have hthi : LT.lt t hi := lt_trans ht1 h1h
              refine ⟨fun _ => t, ?_, ?_⟩
              · refine ⟨⟨?_, ?_⟩, hmt, ?_⟩
                · rcases hlo_ac with heq | hlt
                  · rw [← heq]
                    exact lt_trans hm_lo hmt
                  · exact lt_trans hlt (lt_trans hm_lo hmt)
                · exact hbc
                · intro hex
                  obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq,
                    hmpc, hpc_t, hmqc, hqc_t, hLT, hGp, hGq, hbadD⟩ := hex
                  have hJpc : openInterval (Endpoint.finite u₀) (Endpoint.finite v₀)
                      (fun _ => pc) :=
                    ⟨lt_trans hmu₀ hmpc, lt_trans hpc_t htv₀⟩
                  have hJqc : openInterval (Endpoint.finite u₀) (Endpoint.finite v₀)
                      (fun _ => qc) :=
                    ⟨lt_trans hmu₀ hmqc, lt_trans hqc_t htv₀⟩
                  exact hNBd₀ ⟨pc, qc, wpc, wqc, hIp, hIq, hJpc, hJqc,
                    hLT, hGp, hGq, hbadD⟩
              · exact ⟨hmt, hthi⟩
            have hub_hiD : IsUpperBound1 SD' hi := by
              intro x hx
              obtain ⟨-, hJx⟩ := hx
              exact Or.inl hJx.right
            have hSD'bd : BoundedAbove1 SD' := ⟨hi, hub_hiD⟩
            obtain ⟨sD, hsSupD⟩ := supCompletenessAux SD'
              ((M.ominimal _).mp hSD'mem) hSD'ne hSD'bd
            have hExceedD : ∀ b : R, LT.lt b sD → ∃ t₁, SD (fun _ => t₁) ∧ LT.lt b t₁ := by
              intro b hbs
              by_contra hcon
              push Not at hcon
              have hub : IsUpperBound1 SD' b := by
                intro x hx
                obtain ⟨hSDx, -⟩ := hx
                have e : x = fun _ => Power.coord1 x := ptLam x
                rw [e] at hSDx
                rcases lt_trichotomy (Power.coord1 x) b with h | h | h
                · have hlt := h
                  exact Or.inl hlt
                · have heq := h
                  exact Or.inr heq
                · have hlt := h
                  exact False.elim (not_le_of_gt hlt (hcon _ hSDx))
              rcases hsSupD.2 b hub with h | h
              · exact lt_irrefl _ (lt_trans hbs h)
              · rw [h] at hbs
                exact lt_irrefl _ hbs
            -- Below two upper bounds at once (Dc side).
            have hBetween2D : ∀ z p q : R, LT.lt z p → LT.lt z q →
                ∃ w, LT.lt z w ∧ LT.lt w p ∧ LT.lt w q := by
              intro z p q hzp hzq
              rcases lt_trichotomy p q with h | h | h
              · have hlt := h
                obtain ⟨w, hzw, hwp⟩ := exists_between hzp
                exact ⟨w, hzw, hwp, lt_trans hwp hlt⟩
              · have heq := h
                obtain ⟨w, hzw, hwp⟩ := exists_between hzp
                rw [heq] at hwp ⊢
                exact ⟨w, hzw, hwp, hwp⟩
              · have hlt := h
                obtain ⟨w, hzw, hwq⟩ := exists_between hzq
                exact ⟨w, hzw, lt_trans hwq hlt, hwq⟩
            -- Above two lower bounds at once (Dc side).
            have hBetween3D : ∀ z₁ z₂ p : R, LT.lt z₁ p → LT.lt z₂ p →
                ∃ w, LT.lt z₁ w ∧ LT.lt z₂ w ∧ LT.lt w p := by
              intro z₁ z₂ p h1 h2
              rcases lt_trichotomy z₁ z₂ with h | h | h
              · have hlt := h
                obtain ⟨w, hzw, hwp⟩ := exists_between h2
                exact ⟨w, lt_trans hlt hzw, hzw, hwp⟩
              · have heq := h
                obtain ⟨w, hzw, hwp⟩ := exists_between h2
                refine ⟨w, ?_, hzw, hwp⟩
                rw [heq]
                exact hzw
              · have hlt := h
                obtain ⟨w, hzw, hwp⟩ := exists_between h1
                exact ⟨w, hzw, lt_trans hlt hzw, hwp⟩
            rcases hsSupD.2 hi hub_hiD with hlt | heq
            · exfalso
              have hmsD : LT.lt m sD := by
                have hwit : ∃ t, SD' t := hSD'ne
                have hmc : LT.lt m (Power.coord1 (hSD'ne.choose)) :=
                  ((hSD'ne.choose_spec).1).2.1
                rcases hsSupD.1 (hSD'ne.choose) (hSD'ne.choose_spec) with h | h
                · exact lt_trans hmc h
                · rw [h] at hmc
                  exact hmc
              have hJsD : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => sD) :=
                ⟨lt_trans hm_lo hmsD, hlt⟩
              have hIsD : I' (fun _ => sD) := hIcon _ hJsD
              obtain ⟨hJ₀sD, hIsDI⟩ := hIsD
              obtain ⟨-, -, csD, dsD, hcsD, hsdD, hNBd⟩ := hDcon _ hJsD
              have hcsD' : LT.lt csD sD := hcsD
              have hsdD' : LT.lt sD dsD := hsdD
              obtain ⟨t', ht'sD, ht'dD, ht'hD⟩ := hBetween2D sD dsD hi hsdD' hlt
              -- Decreasing on [m, t'] (helper).
              have hDecT'D : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                  LT.lt m a → LT.lt a t' → LT.lt m b → LT.lt b t' → LT.lt a b →
                  Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
                intro a b ha hb hma hat hmb hbt hab
                rcases lt_trichotomy b sD with h | h | h
                · have hlt_bs := h
                  obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceedD b hlt_bs
                  exact hEqSD t₁ ht₁S a b ha hb hma
                    (lt_trans hab hbt₁) hmb hbt₁ hab
                · have heq_bs := h
                  have has : LT.lt a sD := by
                    rw [← heq_bs]
                    exact hab
                  have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) =
                      ⟨fun _ => sD, hIsDI⟩ :=
                    Subtype.ext (by funext k; exact heq_bs)
                  rw [ept]
                  obtain ⟨w, haw, hwcs, hws⟩ := hBetween3D a csD sD has hcsD'
                  have hJw : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => w) :=
                    ⟨lt_trans hm_lo (lt_trans hma haw), lt_trans hws hlt⟩
                  have hwI : I (fun _ => w) := (hIcon _ hJw).2
                  obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceedD w hws
                  have e1 := hEqSD t₁ ht₁S a w ha hwI hma
                    (lt_trans haw hwt₁) (lt_trans hma haw) hwt₁ haw
                  have e2 := hEqWinDG csD dsD hNBd w sD hwI hIsDI hwcs
                    (lt_trans hws hsdD') hcsD' hsdD' hws
                  exact lt_trans e2 e1
                · have hlt_sb := h
                  rcases lt_trichotomy a sD with h2 | h2 | h2
                  · have hlt_as := h2
                    obtain ⟨w, haw, hwcs, hws⟩ := hBetween3D a csD sD hlt_as hcsD'
                    have hJw : openInterval (Endpoint.finite lo)
                        (Endpoint.finite hi) (fun _ => w) :=
                      ⟨lt_trans hm_lo (lt_trans hma haw), lt_trans hws hlt⟩
                    have hwI : I (fun _ => w) := (hIcon _ hJw).2
                    obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceedD w hws
                    have e1 := hEqSD t₁ ht₁S a w ha hwI hma
                      (lt_trans haw hwt₁) (lt_trans hma haw) hwt₁ haw
                    have e2 := hEqWinDG csD dsD hNBd w b hwI hb hwcs
                      (lt_trans hws (lt_trans hlt_sb (lt_trans hbt ht'dD)))
                      (lt_trans hcsD' hlt_sb) (lt_trans hbt ht'dD)
                      (lt_trans hws hlt_sb)
                    exact lt_trans e2 e1
                  · have heq_as := h2
                    have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) =
                        ⟨fun _ => sD, hIsDI⟩ :=
                      Subtype.ext (by funext k; exact heq_as)
                    rw [ept]
                    exact hEqWinDG csD dsD hNBd sD b hIsDI hb hcsD' hsdD'
                      (lt_trans hcsD' hlt_sb) (lt_trans hbt ht'dD) hlt_sb
                  · have hlt_sa := h2
                    exact hEqWinDG csD dsD hNBd a b ha hb
                      (lt_trans hcsD' hlt_sa) (lt_trans hat ht'dD)
                      (lt_trans hcsD' (lt_trans hlt_sa hab)) (lt_trans hbt ht'dD) hab
              have hT'D : SD (fun _ => t') := by
                refine ⟨⟨?_, ?_⟩, lt_trans hmsD ht'sD, ?_⟩
                · rcases hlo_ac with heq2 | hlt2
                  · rw [← heq2]
                    exact lt_trans hm_lo (lt_trans hmsD ht'sD)
                  · exact lt_trans hlt2 (lt_trans hm_lo (lt_trans hmsD ht'sD))
                · rcases hhi_bc with heq2 | hlt2
                  · rw [← heq2]
                    exact ht'hD
                  · exact lt_trans ht'hD hlt2
                · intro hex
                  obtain ⟨a, b, wpc, wqc, hIp, hIq, hJp, hJq,
                    hmpc, hpc_t, hmqc, hqc_t, hLT, hGp, hGq, hbadD⟩ := hex
                  have hLt := hDecT'D a b hIp hIq hmpc hpc_t hmqc hqc_t hLT
                  have hLtR : LT.lt ((f.toFun ⟨fun _ => b, hIq⟩).1 0)
                      ((f.toFun ⟨fun _ => a, hIp⟩).1 0) := hLt
                  have hwpc := wpcEqVal f a wpc hIp hGp
                  have hwqc := wpcEqVal f b wqc hIq hGq
                  rw [hwpc, hwqc] at hbadD
                  rcases hbadD with h1 | h2
                  · exact lt_irrefl _ (lt_trans h1 hLtR)
                  · have hr : ((f.toFun ⟨fun _ => a, hIp⟩).1 0) =
                        ((f.toFun ⟨fun _ => b, hIq⟩).1 0) :=
                      congrArg (· 0) h2
                    rw [hr] at hLtR
                    exact lt_irrefl _ hLtR
              have ht'SD : SD' (fun _ => t') := ⟨hT'D, ⟨lt_trans hmsD ht'sD, ht'hD⟩⟩
              rcases hsSupD.1 (fun _ => t') ht'SD with h | h
              · exact lt_irrefl _ (lt_trans ht'sD h)
              · rw [← h] at ht'sD
                exact lt_irrefl _ ht'sD
            · subst heq
              have hAnchorRD : ∀ b : R, ∀ (hb : I (fun _ => b)), LT.lt m b → LT.lt b hi →
                  Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨xm, hImm⟩).1 := by
                intro b hb hmb hbhi
                obtain ⟨b₀, hmb₀, hb₀b, hb₀v⟩ := hBetween2D m b v₀ hmb hmv₀
                have hb₀I : I (fun _ => b₀) := by
                  have hJ : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => b₀) :=
                    ⟨lt_trans hm_lo hmb₀, lt_trans hb₀b hbhi⟩
                  exact (hIcon _ hJ).2
                have e1 := hEqWinDG u₀ v₀ hNBd₀ m b₀ hImm hb₀I hmu₀ hmv₀
                  (lt_trans hmu₀ hmb₀) hb₀v hmb₀
                obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceedD b hbhi
                have e2 := hEqSD t₁ ht₁S b₀ b hb₀I hb
                  hmb₀ (lt_trans hb₀b hbt₁) hmb hbt₁ hb₀b
                exact lt_trans e2 e1
              -- Left decreasing-prefix set at m.
              set SLD : Set (Power R 1) := fun c : Power R 1 =>
                openInterval (Endpoint.finite ac) (Endpoint.finite bc) c ∧
                LT.lt (Power.coord1 c) m ∧
                ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
                  openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => pc) ∧
                  openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => qc) ∧
                  LT.lt (Power.coord1 c) pc ∧ LT.lt pc m ∧
                  LT.lt (Power.coord1 c) qc ∧ LT.lt qc m ∧
                  LT.lt pc qc ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => pc) (fun _ => wpc)) ∧
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => qc) (fun _ => wqc)) ∧
                  (Lt1 (fun _ => wpc) (fun _ => wqc) ∨
                    ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) with hSLDdef
              have hSLDmem : M.S 1 SLD := decPrefixLDefinable M f ac bc m
              have hEqSLD : ∀ t : R, SLD (fun _ => t) → ∀ a b : R,
                  ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                  LT.lt t a → LT.lt a m → LT.lt t b → LT.lt b m → LT.lt a b →
                  Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
                intro t hT a b ha hb hta ham htb hbm hab
                obtain ⟨hJt, htm, hNV⟩ := hT
                have hac_a : LT.lt ac a := lt_trans hJt.left hta
                have hac_b : LT.lt ac b := lt_trans hJt.left htb
                have hbc_a : LT.lt a bc := by
                  have hmbc : LT.lt m bc := hJ₀m.right
                  exact lt_trans ham hmbc
                have hbc_b : LT.lt b bc := by
                  have hmbc : LT.lt m bc := hJ₀m.right
                  exact lt_trans hbm hmbc
                rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                    ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
                · have hlt := h
                  exfalso
                  apply hNV
                  refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                    (f.toFun ⟨fun _ => b, hb⟩).1 0,
                    ha, hb, ⟨hac_a, hbc_a⟩, ⟨hac_b, hbc_b⟩,
                    hta, ham, htb, hbm, hab,
                    graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
                  exact hlt
                · have heq := h
                  exfalso
                  apply hNV
                  refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                    (f.toFun ⟨fun _ => b, hb⟩).1 0,
                    ha, hb, ⟨hac_a, hbc_a⟩, ⟨hac_b, hbc_b⟩,
                    hta, ham, htb, hbm, hab,
                    graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
                  exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
                · have hlt := h
                  exact hlt
              set SLD' : Set (Power R 1) := SLD ∩
                (openInterval (Endpoint.finite lo) (Endpoint.finite m)) with hSLD'def
              have hSLD'mem : M.S 1 SLD' :=
                M.inter_mem hSLDmem
                  ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _))
              have hSLD'ne : SLD'.Nonempty := by
                obtain ⟨t, hlot, htu₀, htm⟩ := hBetween3D lo u₀ m hm_lo hmu₀
                have htv₀ : LT.lt t v₀ := lt_trans htm hmv₀
                refine ⟨fun _ => t, ?_, ?_⟩
                · refine ⟨⟨?_, ?_⟩, htm, ?_⟩
                  · rcases hlo_ac with heq | hlt
                    · rw [← heq]
                      exact hlot
                    · exact lt_trans hlt hlot
                  · exact lt_trans htm (hJ₀m.right)
                  · intro hex
                    obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq,
                      hTPC, hPCm, hTQC, hQCm, hLT, hGp, hGq, hbadD⟩ := hex
                    have hJpc : openInterval (Endpoint.finite u₀) (Endpoint.finite v₀)
                        (fun _ => pc) :=
                      ⟨lt_trans htu₀ hTPC, lt_trans hPCm hmv₀⟩
                    have hJqc : openInterval (Endpoint.finite u₀) (Endpoint.finite v₀)
                        (fun _ => qc) :=
                      ⟨lt_trans htu₀ hTQC, lt_trans hQCm hmv₀⟩
                    exact hNBd₀ ⟨pc, qc, wpc, wqc, hIp, hIq, hJpc, hJqc,
                      hLT, hGp, hGq, hbadD⟩
                · exact ⟨hlot, htm⟩
              have hlb_loD : IsLowerBound1 SLD' lo := by
                intro x hx
                obtain ⟨-, hJx⟩ := hx
                exact Or.inl hJx.left
              have hSLD'bd : BoundedBelow1 SLD' := ⟨lo, hlb_loD⟩
              obtain ⟨sL, hsInf⟩ := infCompletenessAux SLD'
                ((M.ominimal _).mp hSLD'mem) hSLD'ne hSLD'bd
              have hExceedLD : ∀ a : R, LT.lt sL a → ∃ t₁, SLD (fun _ => t₁) ∧ LT.lt t₁ a := by
                intro a has
                by_contra hcon
                push Not at hcon
                have hlb : IsLowerBound1 SLD' a := by
                  intro x hx
                  obtain ⟨hSLx, -⟩ := hx
                  have e : x = fun _ => Power.coord1 x := ptLam x
                  rw [e] at hSLx
                  rcases lt_trichotomy a (Power.coord1 x) with h | h | h
                  · have hlt := h
                    exact Or.inl hlt
                  · have heq := h
                    exact Or.inr heq.symm
                  · have hlt := h
                    exact False.elim (not_le_of_gt hlt (hcon _ hSLx))
                rcases hsInf.2 a hlb with h | h
                · exact lt_irrefl _ (lt_trans has h)
                · rw [h] at has
                  exact lt_irrefl _ has
              rcases hsInf.2 lo hlb_loD with hlt | heq
              · exfalso
                have hslm : LT.lt sL m := by
                  have hwit : ∃ t, SLD' t := hSLD'ne
                  rcases hsInf.1 (hSLD'ne.choose) (hSLD'ne.choose_spec) with h | h
                  · exact lt_trans h ((hSLD'ne.choose_spec).2).right
                  · rw [← h]
                    exact ((hSLD'ne.choose_spec).2).right
                have hJsL : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => sL) :=
                  ⟨hlt, lt_trans hslm hm_hi⟩
                have hIsL : I' (fun _ => sL) := hIcon _ hJsL
                obtain ⟨hJ₀sL, hIsLI⟩ := hIsL
                have hBsLD : C (fun _ => sL) ∨ U (fun _ => sL) ∨ Dc (fun _ => sL) := by
                  by_contra hcon
                  have hBad : Bad (fun _ => sL) := by
                    rw [hBaddef]
                    refine ⟨hIcon _ hJsL, ?_⟩
                    intro hc
                    rcases hc with hc | hc | hc
                    · exact hcon (Or.inl hc)
                    · exact hcon (Or.inr (Or.inl hc))
                    · exact hcon (Or.inr (Or.inr hc))
                  exact (hNB _ hJsL) hBad
                rcases hBsLD with hCs | hUs | hDs
                · -- C window at sL meets approached decrease: contradiction.
                  obtain ⟨-, -, csC, dsC, hcsC, hsdC, hNBC⟩ := hCs
                  have hcsC' : LT.lt csC sL := hcsC
                  have hsdC' : LT.lt sL dsC := hsdC
                  have hEqCU : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                      LT.lt csC a → LT.lt a dsC → LT.lt csC b → LT.lt b dsC →
                      (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
                    intro a b ha hb hau hav hbu hbv
                    by_contra hne
                    apply hNBC
                    refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                      (f.toFun ⟨fun _ => b, hb⟩).1 0,
                      ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩,
                      graphAppendConst f a ha, graphAppendConst f b hb, ?_⟩
                    intro heq
                    apply hne
                    have h0 : (f.toFun ⟨fun _ => a, ha⟩).1 0 =
                        (f.toFun ⟨fun _ => b, hb⟩).1 0 :=
                      congrFun heq ⟨0, by decide⟩
                    have e1 : (f.toFun ⟨fun _ => a, ha⟩).1 =
                        (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0) := by
                      funext k
                      have hk : k.val = 0 := by
                        have := k.isLt
                        omega
                      have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
                      rw [ek]
                      rfl
                    have e2 : (f.toFun ⟨fun _ => b, hb⟩).1 =
                        (fun _ : Fin 1 => (f.toFun ⟨fun _ => b, hb⟩).1 0) := by
                      funext k
                      have hk : k.val = 0 := by
                        have := k.isLt
                        omega
                      have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
                      rw [ek]
                      rfl
                    rw [e1, e2, h0]
                  obtain ⟨c0, hsc0, hc0d, hc0m⟩ := hBetween2D sL dsC m hsdC' hslm
                  have hcsCc0 : LT.lt csC c0 := lt_trans hcsC' hsc0
                  obtain ⟨u2, hsu2, hcu2, hu2c0⟩ := hBetween3D sL csC c0 hsc0 hcsCc0
                  obtain ⟨u1, hsu1, hcu1, hu1u2⟩ := hBetween3D sL csC u2 hsu2 hcu2
                  have hu1m : LT.lt u1 m := lt_trans hu1u2 (lt_trans hu2c0 hc0m)
                  have hu2m : LT.lt u2 m := lt_trans hu2c0 hc0m
                  have hu1hi : LT.lt u1 hi := lt_trans hu1m hm_hi
                  have hu2hi : LT.lt u2 hi := lt_trans hu2m hm_hi
                  have hJ1 : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => u1) :=
                    ⟨lt_trans hlt hsu1, hu1hi⟩
                  have hJ2 : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => u2) :=
                    ⟨lt_trans hlt hsu2, hu2hi⟩
                  have hI1 : I (fun _ => u1) := (hIcon _ hJ1).2
                  have hI2 : I (fun _ => u2) := (hIcon _ hJ2).2
                  have eC := hEqCU u1 u2 hI1 hI2 hcu1
                    (lt_trans hu1u2 (lt_trans hu2c0 hc0d)) hcu2 (lt_trans hu2c0 hc0d)
                  obtain ⟨t1, ht1S, htt1⟩ := hExceedLD u1 hsu1
                  have eD := hEqSLD t1 ht1S u1 u2 hI1 hI2 htt1 hu1m
                    (lt_trans htt1 hu1u2) hu2m hu1u2
                  have eDR : LT.lt ((f.toFun ⟨fun _ => u2, hI2⟩).1 0)
                      ((f.toFun ⟨fun _ => u1, hI1⟩).1 0) := eD
                  have h0 := congrArg (· 0) eC
                  rw [h0] at eDR
                  exact lt_irrefl _ eDR
                · -- U window at sL meets approached decrease: contradiction.
                  obtain ⟨-, -, csU, dsU, hcsU, hsdU, hNBU⟩ := hUs
                  have hcsU' : LT.lt csU sL := hcsU
                  have hsdU' : LT.lt sL dsU := hsdU
                  have hEqWinUUD : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                      LT.lt csU a → LT.lt a dsU → LT.lt csU b → LT.lt b dsU → LT.lt a b →
                      Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
                    intro a b ha hb hau hav hbu hbv hab
                    exact hEqWinUGD csU dsU hNBU a b ha hb hau hav hbu hbv hab
                  obtain ⟨c0, hsc0, hc0d, hc0m⟩ := hBetween2D sL dsU m hsdU' hslm
                  have hcsUc0 : LT.lt csU c0 := lt_trans hcsU' hsc0
                  obtain ⟨u2, hsu2, hcu2, hu2c0⟩ := hBetween3D sL csU c0 hsc0 hcsUc0
                  obtain ⟨u1, hsu1, hcu1, hu1u2⟩ := hBetween3D sL csU u2 hsu2 hcu2
                  have hu1m : LT.lt u1 m := lt_trans hu1u2 (lt_trans hu2c0 hc0m)
                  have hu2m : LT.lt u2 m := lt_trans hu2c0 hc0m
                  have hu1hi : LT.lt u1 hi := lt_trans hu1m hm_hi
                  have hu2hi : LT.lt u2 hi := lt_trans hu2m hm_hi
                  have hJ1 : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => u1) :=
                    ⟨lt_trans hlt hsu1, hu1hi⟩
                  have hJ2 : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => u2) :=
                    ⟨lt_trans hlt hsu2, hu2hi⟩
                  have hI1 : I (fun _ => u1) := (hIcon _ hJ1).2
                  have hI2 : I (fun _ => u2) := (hIcon _ hJ2).2
                  obtain ⟨t1, ht1S, htt1⟩ := hExceedLD u1 hsu1
                  have eD := hEqSLD t1 ht1S u1 u2 hI1 hI2 htt1 hu1m
                    (lt_trans htt1 hu1u2) hu2m hu1u2
                  have eI := hEqWinUUD u1 u2 hI1 hI2 hcu1
                    (lt_trans hu1u2 (lt_trans hu2c0 hc0d)) hcu2 (lt_trans hu2c0 hc0d) hu1u2
                  have eIR : LT.lt ((f.toFun ⟨fun _ => u1, hI1⟩).1 0)
                      ((f.toFun ⟨fun _ => u2, hI2⟩).1 0) := eI
                  have eDR : LT.lt ((f.toFun ⟨fun _ => u2, hI2⟩).1 0)
                      ((f.toFun ⟨fun _ => u1, hI1⟩).1 0) := eD
                  exact lt_irrefl _ (lt_trans eIR eDR)
                · -- Dc window at sL: decreasing extends left past sL.
                  obtain ⟨-, -, csD, dsD, hcsD, hsdD, hNBD⟩ := hDs
                  have hcsD' : LT.lt csD sL := hcsD
                  have hsdD' : LT.lt sL dsD := hsdD
                  obtain ⟨t', hct', hlot', ht'sL⟩ := hBetween3D csD lo sL hcsD' hlt
                  have hDecTL : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                      LT.lt t' a → LT.lt a m → LT.lt t' b → LT.lt b m → LT.lt a b →
                      Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
                    intro a b ha hb hta ham htb hbm hab
                    rcases lt_trichotomy b sL with h | h | h
                    · have hlt_bs := h
                      exact hEqWinDG csD dsD hNBD a b ha hb
                        (lt_trans hct' hta) (lt_trans (lt_trans hab hlt_bs) hsdD')
                        (lt_trans hct' htb) (lt_trans hlt_bs hsdD') hab
                    · have heq_bs := h
                      have has : LT.lt a sL := by
                        rw [← heq_bs]
                        exact hab
                      have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) =
                          ⟨fun _ => sL, hIsLI⟩ :=
                        Subtype.ext (by funext k; exact heq_bs)
                      rw [ept]
                      obtain ⟨w, haw, hwcs, hws⟩ := hBetween3D a csD sL has hcsD'
                      have hJw : openInterval (Endpoint.finite lo)
                          (Endpoint.finite hi) (fun _ => w) :=
                        ⟨lt_trans hlot' (lt_trans hta haw), lt_trans hws (lt_trans hslm hm_hi)⟩
                      have hwI : I (fun _ => w) := (hIcon _ hJw).2
                      have e1 := hEqWinDG csD dsD hNBD a w ha hwI
                        (lt_trans hct' hta) (lt_trans haw (lt_trans hws hsdD'))
                        (lt_trans (lt_trans hct' hta) haw) (lt_trans hws hsdD') haw
                      have e2 := hEqWinDG csD dsD hNBD w sL hwI hIsLI hwcs
                        (lt_trans hws hsdD') hcsD' hsdD' hws
                      exact lt_trans e2 e1
                    · have hlt_sb := h
                      rcases lt_trichotomy a sL with h2 | h2 | h2
                      · have hlt_as := h2
                        have e1 := hEqWinDG csD dsD hNBD a sL ha hIsLI
                          (lt_trans hct' hta) (lt_trans hlt_as hsdD')
                          hcsD' hsdD' hlt_as
                        obtain ⟨w, hsw, hwb, hwds⟩ := hBetween2D sL b dsD hlt_sb hsdD'
                        have hJw : openInterval (Endpoint.finite lo)
                            (Endpoint.finite hi) (fun _ => w) :=
                          ⟨lt_trans hlt hsw, lt_trans hwb (lt_trans hbm hm_hi)⟩
                        have hwI : I (fun _ => w) := (hIcon _ hJw).2
                        have e2a := hEqWinDG csD dsD hNBD sL w hIsLI hwI
                          hcsD' hsdD' (lt_trans hcsD' hsw) hwds hsw
                        obtain ⟨t1, ht1S, hwt1⟩ := hExceedLD w hsw
                        have e2b := hEqSLD t1 ht1S w b hwI hb
                          hwt1 (lt_trans hwb hbm) (lt_trans hwt1 hwb) hbm hwb
                        exact lt_trans e2b (lt_trans e2a e1)
                      · have heq_as := h2
                        have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) =
                            ⟨fun _ => sL, hIsLI⟩ :=
                          Subtype.ext (by funext k; exact heq_as)
                        rw [ept]
                        obtain ⟨w, hsw, hwb, hwds⟩ := hBetween2D sL b dsD hlt_sb hsdD'
                        have hJw : openInterval (Endpoint.finite lo)
                            (Endpoint.finite hi) (fun _ => w) :=
                          ⟨lt_trans hlt hsw, lt_trans hwb (lt_trans hbm hm_hi)⟩
                        have hwI : I (fun _ => w) := (hIcon _ hJw).2
                        have e1 := hEqWinDG csD dsD hNBD sL w hIsLI hwI
                          hcsD' hsdD' (lt_trans hcsD' hsw) hwds hsw
                        obtain ⟨t1, ht1S, hwt1⟩ := hExceedLD w hsw
                        have e2 := hEqSLD t1 ht1S w b hwI hb
                          hwt1 (lt_trans hwb hbm) (lt_trans hwt1 hwb) hbm hwb
                        exact lt_trans e2 e1
                      · have hlt_sa := h2
                        obtain ⟨t1, ht1S, htt1⟩ := hExceedLD a hlt_sa
                        exact hEqSLD t1 ht1S a b ha hb htt1 ham
                          (lt_trans htt1 hab) hbm hab
                  have hT'LD : SLD (fun _ => t') := by
                    refine ⟨⟨?_, ?_⟩, lt_trans ht'sL hslm, ?_⟩
                    · rcases hlo_ac with heq2 | hlt2
                      · rw [← heq2]
                        exact hlot'
                      · exact lt_trans hlt2 hlot'
                    · exact lt_trans ht'sL (lt_trans hslm (hJ₀m.right))
                    · intro hex
                      obtain ⟨a, b, wpc, wqc, hIp, hIq, hJp, hJq,
                        hta, ham, htb, hbm, hLT, hGp, hGq, hbadD⟩ := hex
                      have hLt := hDecTL a b hIp hIq hta ham htb hbm hLT
                      have hLtR : LT.lt ((f.toFun ⟨fun _ => b, hIq⟩).1 0)
                          ((f.toFun ⟨fun _ => a, hIp⟩).1 0) := hLt
                      have hwpc := wpcEqVal f a wpc hIp hGp
                      have hwqc := wpcEqVal f b wqc hIq hGq
                      rw [hwpc, hwqc] at hbadD
                      rcases hbadD with h1 | h2
                      · exact lt_irrefl _ (lt_trans h1 hLtR)
                      · have hr : ((f.toFun ⟨fun _ => a, hIp⟩).1 0) =
                            ((f.toFun ⟨fun _ => b, hIq⟩).1 0) :=
                          congrArg (· 0) h2
                        rw [hr] at hLtR
                        exact lt_irrefl _ hLtR
                  have ht'SLD' : SLD' (fun _ => t') := ⟨hT'LD, ⟨hlot', lt_trans ht'sL hslm⟩⟩
                  rcases hsInf.1 (fun _ => t') ht'SLD' with h | h
                  · exact lt_irrefl _ (lt_trans h ht'sL)
                  · rw [← h] at ht'sL
                    exact lt_irrefl _ ht'sL
              · subst heq
                have hAnchorLD : ∀ a : R, ∀ (ha : I (fun _ => a)), LT.lt lo a → LT.lt a m →
                    Lt1 (f.toFun ⟨xm, hImm⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
                  intro a ha hlo_a ham
                  obtain ⟨b₀, hab₀, hub₀, hb₀m⟩ := hBetween3D a u₀ m ham hmu₀
                  have hb₀v : LT.lt b₀ v₀ := lt_trans hb₀m hmv₀
                  have hb₀I : I (fun _ => b₀) := by
                    have hJ : openInterval (Endpoint.finite lo)
                        (Endpoint.finite hi) (fun _ => b₀) :=
                      ⟨lt_trans hlo_a hab₀, lt_trans hb₀m hm_hi⟩
                    exact (hIcon _ hJ).2
                  obtain ⟨t₁, ht₁S, htt₁⟩ := hExceedLD a hlo_a
                  have e1 := hEqSLD t₁ ht₁S a b₀ ha hb₀I htt₁ ham
                    (lt_trans htt₁ hab₀) hb₀m hab₀
                  have e2 := hEqWinDG u₀ v₀ hNBd₀ b₀ m hb₀I hImm hub₀ hb₀v
                    hmu₀ hmv₀ hb₀m
                  exact lt_trans e2 e1
                have hDecR : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                    LT.lt lo a → LT.lt a hi → LT.lt lo b → LT.lt b hi → LT.lt a b →
                    Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
                  intro a b ha hb hlo_a hahi hlo_b hbhi hab
                  rcases lt_trichotomy b m with h | h | h
                  · have hlt_bm := h
                    obtain ⟨t₁, ht₁S, htt₁⟩ := hExceedLD a hlo_a
                    exact hEqSLD t₁ ht₁S a b ha hb htt₁ (lt_trans hab hlt_bm)
                      (lt_trans htt₁ hab) hlt_bm hab
                  · have heq_bm := h
                    have ham : LT.lt a m := by
                      rw [← heq_bm]
                      exact hab
                    have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) = ⟨xm, hImm⟩ :=
                      Subtype.ext (congrArg (fun r : R => (fun _ : Fin 1 => r)) heq_bm)
                    rw [ept]
                    exact hAnchorLD a ha hlo_a ham
                  · have hlt_mb := h
                    rcases lt_trichotomy a m with h2 | h2 | h2
                    · have hlt_am := h2
                      exact lt_trans (hAnchorRD b hb hlt_mb hbhi) (hAnchorLD a ha hlo_a hlt_am)
                    · have heq_am := h2
                      have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) = ⟨xm, hImm⟩ :=
                        Subtype.ext (congrArg (fun r : R => (fun _ : Fin 1 => r)) heq_am)
                      rw [ept]
                      exact hAnchorRD b hb hlt_mb hbhi
                    · have hlt_ma := h2
                      obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceedD b hbhi
                      exact hEqSD t₁ ht₁S a b ha hb hlt_ma (lt_trans hab hbt₁)
                        (lt_trans hlt_ma hab) hbt₁ hab
                refine Or.inr ⟨Or.inr ?_, ?_⟩
                · intro x hxI hJx y hyI hJy hlt
                  have hxI2 : I (fun _ => Power.coord1 x) := by
                    rw [← ptLam x]
                    exact hxI
                  have hyI2 : I (fun _ => Power.coord1 y) := by
                    rw [← ptLam y]
                    exact hyI
                  have hJx2 : openInterval (Endpoint.finite lo) (Endpoint.finite hi)
                      (fun _ => Power.coord1 x) := by
                    rw [ptLam x] at hJx
                    exact hJx
                  have hJy2 : openInterval (Endpoint.finite lo) (Endpoint.finite hi)
                      (fun _ => Power.coord1 y) := by
                    rw [ptLam y] at hJy
                    exact hJy
                  have hlt' : LT.lt (Power.coord1 x) (Power.coord1 y) := hlt
                  have eX : (⟨x, hxI⟩ : {x : Power R 1 // I x}) =
                      ⟨fun _ => Power.coord1 x, hxI2⟩ := Subtype.ext (ptLam x)
                  have eY : (⟨y, hyI⟩ : {x : Power R 1 // I x}) =
                      ⟨fun _ => Power.coord1 y, hyI2⟩ := Subtype.ext (ptLam y)
                  rw [eX, eY]
                  exact hDecR _ _ _ _ hJx2.left hJx2.right hJy2.left hJy2.right hlt'
                · -- Continuity: no Disc point lies strictly inside the piece.
                  intro x hJx
                  have hxI : I x := (hIcon x hJx).2
                  by_contra hNC
                  obtain ⟨t, hWt⟩ :=
                    Monotonicity_Theorem.disc_witness_aux M f x hxI hNC
                  have hmem : Power.coord1 x ∈ DiscList := hDiscListMp x ⟨t, hWt⟩
                  have hE : Power.coord1 x ∈ E := hDisc'E _ hmem
                  exact hconsec _ hE ⟨hJx.left, hJx.right⟩
        · -- Case U: increasing covers the piece.
          obtain ⟨m, hm_lo, hm_hi⟩ := exists_between hlohi
          set xm : Power R 1 := fun _ => m with hxmdef
          have hJm : openInterval (Endpoint.finite lo) (Endpoint.finite hi) xm :=
            ⟨hm_lo, hm_hi⟩
          obtain ⟨hJ₀m, hImm, u₀, v₀, hu₀, hv₀, hNBu₀⟩ := hUcon xm hJm
          have hmu₀ : LT.lt u₀ m := hu₀
          have hmv₀ : LT.lt m v₀ := hv₀
          -- Increasing from a U-violation-free window.
          have hEqWinUG : ∀ u v : R,
              (¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
                openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
                openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
                LT.lt pc qc ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => pc) (fun _ => wpc)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => qc) (fun _ => wqc)) ∧
                (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
                  ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)))) →
              ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
              LT.lt u a → LT.lt a v → LT.lt u b → LT.lt b v → LT.lt a b →
              Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
            intro u v hNBw a b ha hb hau hav hbu hbv hab
            rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
            · have hlt := h
              exact hlt
            · have heq := h
              exfalso
              apply hNBw
              refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                (f.toFun ⟨fun _ => b, hb⟩).1 0,
                ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
              exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
            · have hlt := h
              exfalso
              apply hNBw
              refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                (f.toFun ⟨fun _ => b, hb⟩).1 0,
                ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
              exact hlt
          -- Right increasing-prefix set at m.
          set SU : Set (Power R 1) := fun c : Power R 1 =>
            openInterval (Endpoint.finite ac) (Endpoint.finite bc) c ∧
            LT.lt m (Power.coord1 c) ∧
            ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
              openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => pc) ∧
              openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => qc) ∧
              LT.lt m pc ∧ LT.lt pc (Power.coord1 c) ∧
              LT.lt m qc ∧ LT.lt qc (Power.coord1 c) ∧
              LT.lt pc qc ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ => pc) (fun _ => wpc)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ => qc) (fun _ => wqc)) ∧
              (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
                ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) with hSUdef
          have hSUmem : M.S 1 SU := incPrefixRDefinable M f ac bc m
          -- Increasing on an increasing-prefix segment.
          have hEqSU : ∀ t : R, SU (fun _ => t) → ∀ a b : R,
              ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
              LT.lt m a → LT.lt a t → LT.lt m b → LT.lt b t → LT.lt a b →
              Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
            intro t hT a b ha hb hma hat hmb hbt hab
            obtain ⟨hJt, hmt, hNV⟩ := hT
            have hta : LT.lt t bc := hJt.right
            have hac_a : LT.lt ac a := by
              rcases hlo_ac with heq | hlt
              · rw [← heq]
                exact lt_trans hm_lo hma
              · exact lt_trans hlt (lt_trans hm_lo hma)
            have hac_b : LT.lt ac b := by
              rcases hlo_ac with heq | hlt
              · rw [← heq]
                exact lt_trans hm_lo hmb
              · exact lt_trans hlt (lt_trans hm_lo hmb)
            rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
            · have hlt := h
              exact hlt
            · have heq := h
              exfalso
              apply hNV
              refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                (f.toFun ⟨fun _ => b, hb⟩).1 0,
                ha, hb, ⟨hac_a, lt_trans hat hta⟩, ⟨hac_b, lt_trans hbt hta⟩,
                hma, hat, hmb, hbt, hab,
                graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
              exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
            · have hlt := h
              exfalso
              apply hNV
              refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                (f.toFun ⟨fun _ => b, hb⟩).1 0,
                ha, hb, ⟨hac_a, lt_trans hat hta⟩, ⟨hac_b, lt_trans hbt hta⟩,
                hma, hat, hmb, hbt, hab,
                graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
              exact hlt
          have hmin2U : ∀ p q : R, LT.lt m p → LT.lt m q →
              ∃ t, LT.lt m t ∧ LT.lt t p ∧ LT.lt t q := by
            intro p q hmp hmq
            rcases lt_trichotomy p q with h | h | h
            · have hlt := h
              obtain ⟨t, hmt, htp⟩ := exists_between hmp
              exact ⟨t, hmt, htp, lt_trans htp hlt⟩
            · have heq := h
              obtain ⟨t, hmt, htp⟩ := exists_between hmp
              rw [heq] at htp ⊢
              exact ⟨t, hmt, htp, htp⟩
            · have hlt := h
              obtain ⟨t, hmt, htq⟩ := exists_between hmq
              exact ⟨t, hmt, lt_trans htq hlt, htq⟩
          set SU' : Set (Power R 1) := SU ∩
            (openInterval (Endpoint.finite m) (Endpoint.finite hi)) with hSU'def
          have hSU'mem : M.S 1 SU' :=
            M.inter_mem hSUmem
              ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _))
          have hSU'ne : SU'.Nonempty := by
            obtain ⟨t₁, hm1, h1v, h1h⟩ := hmin2U v₀ hi hmv₀ hm_hi
            obtain ⟨t, hmt, ht1, hbc⟩ := hmin2U t₁ bc hm1 hJ₀m.right
            have htv₀ : LT.lt t v₀ := lt_trans ht1 h1v
            have hthi : LT.lt t hi := lt_trans ht1 h1h
            refine ⟨fun _ => t, ?_, ?_⟩
            · refine ⟨⟨?_, ?_⟩, hmt, ?_⟩
              · rcases hlo_ac with heq | hlt
                · rw [← heq]
                  exact lt_trans hm_lo hmt
                · exact lt_trans hlt (lt_trans hm_lo hmt)
              · exact hbc
              · intro hex
                apply hNBu₀
                obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq,
                  hmpc, hpc_t, hmqc, hqc_t, hLT, hGp, hGq, hbadU⟩ := hex
                refine ⟨pc, qc, wpc, wqc, hIp, hIq, ?_, ?_,
                  hLT, hGp, hGq, hbadU⟩
                · exact ⟨lt_trans hmu₀ hmpc, lt_trans hpc_t htv₀⟩
                · exact ⟨lt_trans hmu₀ hmqc, lt_trans hqc_t htv₀⟩
            · exact ⟨hmt, hthi⟩
          have hub_hi : IsUpperBound1 SU' hi := by
            intro x hx
            obtain ⟨-, hJx⟩ := hx
            exact Or.inl hJx.right
          have hSU'bd : BoundedAbove1 SU' := ⟨hi, hub_hi⟩
          obtain ⟨s, hsSup⟩ := supCompletenessAux SU'
            ((M.ominimal _).mp hSU'mem) hSU'ne hSU'bd
          have hExceedU : ∀ b : R, LT.lt b s → ∃ t₁, SU (fun _ => t₁) ∧ LT.lt b t₁ := by
            intro b hbs
            by_contra hcon
            push Not at hcon
            have hub : IsUpperBound1 SU' b := by
              intro x hx
              obtain ⟨hSUx, -⟩ := hx
              have e : x = fun _ => Power.coord1 x := ptLam x
              rw [e] at hSUx
              rcases lt_trichotomy (Power.coord1 x) b with h | h | h
              · have hlt := h
                exact Or.inl hlt
              · have heq := h
                exact Or.inr heq
              · have hlt := h
                exact False.elim (not_le_of_gt hlt (hcon _ hSUx))
            rcases hsSup.2 b hub with h | h
            · exact lt_irrefl _ (lt_trans hbs h)
            · rw [h] at hbs
              exact lt_irrefl _ hbs
          -- Below two upper bounds at once (U side).
          have hBetween2U : ∀ z p q : R, LT.lt z p → LT.lt z q →
              ∃ w, LT.lt z w ∧ LT.lt w p ∧ LT.lt w q := by
            intro z p q hzp hzq
            rcases lt_trichotomy p q with h | h | h
            · have hlt := h
              obtain ⟨w, hzw, hwp⟩ := exists_between hzp
              exact ⟨w, hzw, hwp, lt_trans hwp hlt⟩
            · have heq := h
              obtain ⟨w, hzw, hwp⟩ := exists_between hzp
              rw [heq] at hwp ⊢
              exact ⟨w, hzw, hwp, hwp⟩
            · have hlt := h
              obtain ⟨w, hzw, hwq⟩ := exists_between hzq
              exact ⟨w, hzw, lt_trans hwq hlt, hwq⟩
          -- Above two lower bounds at once (U side).
          have hBetween3U : ∀ z₁ z₂ p : R, LT.lt z₁ p → LT.lt z₂ p →
              ∃ w, LT.lt z₁ w ∧ LT.lt z₂ w ∧ LT.lt w p := by
            intro z₁ z₂ p h1 h2
            rcases lt_trichotomy z₁ z₂ with h | h | h
            · have hlt := h
              obtain ⟨w, hzw, hwp⟩ := exists_between h2
              exact ⟨w, lt_trans hlt hzw, hzw, hwp⟩
            · have heq := h
              obtain ⟨w, hzw, hwp⟩ := exists_between h2
              refine ⟨w, ?_, hzw, hwp⟩
              rw [heq]
              exact hzw
            · have hlt := h
              obtain ⟨w, hzw, hwp⟩ := exists_between h1
              exact ⟨w, hzw, lt_trans hlt hzw, hwp⟩
          rcases hsSup.2 hi hub_hi with hlt | heq
          · exfalso
            have hms : LT.lt m s := by
              have hwit : ∃ t, SU' t := hSU'ne
              have hmc : LT.lt m (Power.coord1 (hSU'ne.choose)) :=
                ((hSU'ne.choose_spec).1).2.1
              rcases hsSup.1 (hSU'ne.choose) (hSU'ne.choose_spec) with h | h
              · exact lt_trans hmc h
              · rw [h] at hmc
                exact hmc
            have hJs : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => s) :=
              ⟨lt_trans hm_lo hms, hlt⟩
            have hIs : I' (fun _ => s) := hIcon _ hJs
            obtain ⟨hJ₀s, hIsI⟩ := hIs
            obtain ⟨-, -, cs, ds, hcs, hsd, hNBu⟩ := hUcon _ hJs
            have hcs' : LT.lt cs s := hcs
            have hsd' : LT.lt s ds := hsd
            obtain ⟨t', ht's, ht'd, ht'h⟩ := hBetween2U s ds hi hsd' hlt
            -- Increasing on [m, t'] (helper).
            have hIncT' : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                LT.lt m a → LT.lt a t' → LT.lt m b → LT.lt b t' → LT.lt a b →
                Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
              intro a b ha hb hma hat hmb hbt hab
              rcases lt_trichotomy b s with h | h | h
              · have hlt_bs := h
                obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceedU b hlt_bs
                exact hEqSU t₁ ht₁S a b ha hb hma
                  (lt_trans hab hbt₁) hmb hbt₁ hab
              · have heq_bs := h
                have has : LT.lt a s := by
                  rw [← heq_bs]
                  exact hab
                have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) =
                    ⟨fun _ => s, hIsI⟩ :=
                  Subtype.ext (by funext k; exact heq_bs)
                rw [ept]
                obtain ⟨w, haw, hwcs, hws⟩ := hBetween3U a cs s has hcs'
                have hmw : LT.lt m w := lt_trans hma haw
                have hwhi : LT.lt w hi := lt_trans hws hlt
                have hJw : openInterval (Endpoint.finite lo)
                    (Endpoint.finite hi) (fun _ => w) :=
                  ⟨lt_trans hm_lo hmw, hwhi⟩
                have hwI : I (fun _ => w) := (hIcon _ hJw).2
                obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceedU w hws
                have e1 := hEqSU t₁ ht₁S a w ha hwI hma
                  (lt_trans haw hwt₁) (lt_trans hma haw) hwt₁ haw
                have e2 := hEqWinUG cs ds hNBu w s hwI hIsI hwcs
                  (lt_trans hws hsd') hcs' hsd' hws
                exact lt_trans e1 e2
              · have hlt_sb := h
                rcases lt_trichotomy a s with h2 | h2 | h2
                · have hlt_as := h2
                  obtain ⟨w, haw, hwcs, hws⟩ := hBetween3U a cs s hlt_as hcs'
                  have hmw : LT.lt m w := lt_trans hma haw
                  have hwhi : LT.lt w hi := lt_trans hws hlt
                  have hJw : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => w) :=
                    ⟨lt_trans hm_lo hmw, hwhi⟩
                  have hwI : I (fun _ => w) := (hIcon _ hJw).2
                  obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceedU w hws
                  have e1 := hEqSU t₁ ht₁S a w ha hwI hma
                    (lt_trans haw hwt₁) (lt_trans hma haw) hwt₁ haw
                  have e2 := hEqWinUG cs ds hNBu w b hwI hb hwcs
                    (lt_trans hws (lt_trans hlt_sb (lt_trans hbt ht'd)))
                    (lt_trans hcs' hlt_sb) (lt_trans hbt ht'd)
                    (lt_trans hws hlt_sb)
                  exact lt_trans e1 e2
                · have heq_as := h2
                  have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) =
                      ⟨fun _ => s, hIsI⟩ :=
                    Subtype.ext (by funext k; exact heq_as)
                  rw [ept]
                  exact hEqWinUG cs ds hNBu s b hIsI hb hcs' hsd'
                    (lt_trans hcs' hlt_sb) (lt_trans hbt ht'd) hlt_sb
                · have hlt_sa := h2
                  exact hEqWinUG cs ds hNBu a b ha hb
                    (lt_trans hcs' hlt_sa) (lt_trans hat ht'd)
                    (lt_trans hcs' (lt_trans hlt_sa hab)) (lt_trans hbt ht'd) hab
            have hT' : SU (fun _ => t') := by
              refine ⟨⟨?_, ?_⟩, lt_trans hms ht's, ?_⟩
              · rcases hlo_ac with heq2 | hlt2
                · rw [← heq2]
                  exact lt_trans hm_lo (lt_trans hms ht's)
                · exact lt_trans hlt2 (lt_trans hm_lo (lt_trans hms ht's))
              · rcases hhi_bc with heq2 | hlt2
                · rw [← heq2]
                  exact ht'h
                · exact lt_trans ht'h hlt2
              · intro hex
                obtain ⟨a, b, wpc, wqc, hIp, hIq, hJp, hJq,
                  hmpc, hpc_t, hmqc, hqc_t, hLT, hGp, hGq, hbadU⟩ := hex
                have hLt := hIncT' a b hIp hIq hmpc hpc_t hmqc hqc_t hLT
                have hLtR : LT.lt ((f.toFun ⟨fun _ => a, hIp⟩).1 0)
                    ((f.toFun ⟨fun _ => b, hIq⟩).1 0) := hLt
                have hwpc := wpcEqVal f a wpc hIp hGp
                have hwqc := wpcEqVal f b wqc hIq hGq
                rw [hwpc, hwqc] at hbadU
                rcases hbadU with h1 | h2
                · exact lt_irrefl _ (lt_trans hLtR h1)
                · have hr : ((f.toFun ⟨fun _ => a, hIp⟩).1 0) =
                      ((f.toFun ⟨fun _ => b, hIq⟩).1 0) :=
                    congrArg (· 0) h2
                  rw [hr] at hLtR
                  exact lt_irrefl _ hLtR
            have ht'S : SU' (fun _ => t') := ⟨hT', ⟨lt_trans hms ht's, ht'h⟩⟩
            rcases hsSup.1 (fun _ => t') ht'S with h | h
            · exact lt_irrefl _ (lt_trans ht's h)
            · rw [← h] at ht's
              exact lt_irrefl _ ht's
          · subst heq
            have hAnchorRU : ∀ b : R, ∀ (hb : I (fun _ => b)), LT.lt m b → LT.lt b hi →
                Lt1 (f.toFun ⟨xm, hImm⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
              intro b hb hmb hbhi
              obtain ⟨b₀, hmb₀, hb₀b, hb₀v⟩ := hBetween2U m b v₀ hmb hmv₀
              have hb₀I : I (fun _ => b₀) := by
                have hJ : openInterval (Endpoint.finite lo)
                    (Endpoint.finite hi) (fun _ => b₀) :=
                  ⟨lt_trans hm_lo hmb₀, lt_trans hb₀b hbhi⟩
                exact (hIcon _ hJ).2
              have e1 := hEqWinUG u₀ v₀ hNBu₀ m b₀ hImm hb₀I hmu₀ hmv₀
                (lt_trans hmu₀ hmb₀) hb₀v hmb₀
              obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceedU b hbhi
              have e2 := hEqSU t₁ ht₁S b₀ b hb₀I hb
                hmb₀ (lt_trans hb₀b hbt₁) hmb hbt₁ hb₀b
              exact lt_trans e1 e2
            -- Left increasing-prefix set at m.
            set SLU : Set (Power R 1) := fun c : Power R 1 =>
              openInterval (Endpoint.finite ac) (Endpoint.finite bc) c ∧
              LT.lt (Power.coord1 c) m ∧
              ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
                openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => pc) ∧
                openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => qc) ∧
                LT.lt (Power.coord1 c) pc ∧ LT.lt pc m ∧
                LT.lt (Power.coord1 c) qc ∧ LT.lt qc m ∧
                LT.lt pc qc ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => pc) (fun _ => wpc)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => qc) (fun _ => wqc)) ∧
                (Lt1 (fun _ => wqc) (fun _ => wpc) ∨
                  ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) with hSLUdef
            have hSLUmem : M.S 1 SLU := incPrefixLDefinable M f ac bc m
            have hEqSLU : ∀ t : R, SLU (fun _ => t) → ∀ a b : R,
                ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                LT.lt t a → LT.lt a m → LT.lt t b → LT.lt b m → LT.lt a b →
                Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
              intro t hT a b ha hb hta ham htb hbm hab
              obtain ⟨hJt, htm, hNV⟩ := hT
              have hta2 : LT.lt t bc := hJt.right
              have hac_a : LT.lt ac a := lt_trans hJt.left hta
              have hac_b : LT.lt ac b := lt_trans hJt.left htb
              have hbc_a : LT.lt a bc := by
                have hmbc : LT.lt m bc := hJ₀m.right
                exact lt_trans ham hmbc
              have hbc_b : LT.lt b bc := by
                have hmbc : LT.lt m bc := hJ₀m.right
                exact lt_trans hbm hmbc
              rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                  ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
              · have hlt := h
                exact hlt
              · have heq := h
                exfalso
                apply hNV
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hac_a, hbc_a⟩, ⟨hac_b, hbc_b⟩,
                  hta, ham, htb, hbm, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
                exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
              · have hlt := h
                exfalso
                apply hNV
                refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                  (f.toFun ⟨fun _ => b, hb⟩).1 0,
                  ha, hb, ⟨hac_a, hbc_a⟩, ⟨hac_b, hbc_b⟩,
                  hta, ham, htb, hbm, hab,
                  graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
                exact hlt
            set SLU' : Set (Power R 1) := SLU ∩
              (openInterval (Endpoint.finite lo) (Endpoint.finite m)) with hSLU'def
            have hSLU'mem : M.S 1 SLU' :=
              M.inter_mem hSLUmem
                ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _))
            have hSLU'ne : SLU'.Nonempty := by
              obtain ⟨t, hlot, htu₀, htm⟩ := hBetween3U lo u₀ m hm_lo hmu₀
              -- wait: hBetween3U is 2-lower-1-upper; need lo<t, u₀<t, t<m ✓ exactly that!
              have htv₀ : LT.lt t v₀ := lt_trans htm hmv₀
              refine ⟨fun _ => t, ?_, ?_⟩
              · refine ⟨⟨?_, ?_⟩, htm, ?_⟩
                · rcases hlo_ac with heq | hlt
                  · rw [← heq]
                    exact hlot
                  · exact lt_trans hlt hlot
                · exact lt_trans htm (hJ₀m.right)
                · intro hex
                  obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq,
                    hTPC, hPCm, hTQC, hQCm, hLT, hGp, hGq, hbadU⟩ := hex
                  have hJpc : openInterval (Endpoint.finite u₀) (Endpoint.finite v₀)
                      (fun _ => pc) :=
                    ⟨lt_trans htu₀ hTPC, lt_trans hPCm hmv₀⟩
                  have hJqc : openInterval (Endpoint.finite u₀) (Endpoint.finite v₀)
                      (fun _ => qc) :=
                    ⟨lt_trans htu₀ hTQC, lt_trans hQCm hmv₀⟩
                  exact hNBu₀ ⟨pc, qc, wpc, wqc, hIp, hIq, hJpc, hJqc,
                    hLT, hGp, hGq, hbadU⟩
              · exact ⟨hlot, htm⟩
            have hlb_loU : IsLowerBound1 SLU' lo := by
              intro x hx
              obtain ⟨-, hJx⟩ := hx
              exact Or.inl hJx.left
            have hSLU'bd : BoundedBelow1 SLU' := ⟨lo, hlb_loU⟩
            obtain ⟨sL, hsInf⟩ := infCompletenessAux SLU'
              ((M.ominimal _).mp hSLU'mem) hSLU'ne hSLU'bd
            have hExceedLU : ∀ a : R, LT.lt sL a → ∃ t₁, SLU (fun _ => t₁) ∧ LT.lt t₁ a := by
              intro a has
              by_contra hcon
              push Not at hcon
              have hlb : IsLowerBound1 SLU' a := by
                intro x hx
                obtain ⟨hSLx, -⟩ := hx
                have e : x = fun _ => Power.coord1 x := ptLam x
                rw [e] at hSLx
                rcases lt_trichotomy a (Power.coord1 x) with h | h | h
                · have hlt := h
                  exact Or.inl hlt
                · have heq := h
                  exact Or.inr heq.symm
                · have hlt := h
                  exact False.elim (not_le_of_gt hlt (hcon _ hSLx))
              rcases hsInf.2 a hlb with h | h
              · exact lt_irrefl _ (lt_trans has h)
              · rw [h] at has
                exact lt_irrefl _ has
            rcases hsInf.2 lo hlb_loU with hlt | heq
            · exfalso
              have hslm : LT.lt sL m := by
                have hwit : ∃ t, SLU' t := hSLU'ne
                rcases hsInf.1 (hSLU'ne.choose) (hSLU'ne.choose_spec) with h | h
                · exact lt_trans h ((hSLU'ne.choose_spec).2).right
                · rw [← h]
                  exact ((hSLU'ne.choose_spec).2).right
              have hJsL : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => sL) :=
                ⟨hlt, lt_trans hslm hm_hi⟩
              have hIsL : I' (fun _ => sL) := hIcon _ hJsL
              obtain ⟨hJ₀sL, hIsLI⟩ := hIsL
              have hBsLU : C (fun _ => sL) ∨ U (fun _ => sL) ∨ Dc (fun _ => sL) := by
                by_contra hcon
                have hBad : Bad (fun _ => sL) := by
                  rw [hBaddef]
                  refine ⟨hIcon _ hJsL, ?_⟩
                  intro hc
                  rcases hc with hc | hc | hc
                  · exact hcon (Or.inl hc)
                  · exact hcon (Or.inr (Or.inl hc))
                  · exact hcon (Or.inr (Or.inr hc))
                exact (hNB _ hJsL) hBad
              rcases hBsLU with hCs | hUs | hDs
              · -- C window at sL meets approached increase: contradiction.
                obtain ⟨-, -, csC, dsC, hcsC, hsdC, hNBC⟩ := hCs
                have hcsC' : LT.lt csC sL := hcsC
                have hsdC' : LT.lt sL dsC := hsdC
                have hEqCU : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                    LT.lt csC a → LT.lt a dsC → LT.lt csC b → LT.lt b dsC →
                    (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
                  intro a b ha hb hau hav hbu hbv
                  by_contra hne
                  apply hNBC
                  refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                    (f.toFun ⟨fun _ => b, hb⟩).1 0,
                    ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩,
                    graphAppendConst f a ha, graphAppendConst f b hb, ?_⟩
                  intro heq
                  apply hne
                  have h0 : (f.toFun ⟨fun _ => a, ha⟩).1 0 =
                      (f.toFun ⟨fun _ => b, hb⟩).1 0 :=
                    congrFun heq ⟨0, by decide⟩
                  have e1 : (f.toFun ⟨fun _ => a, ha⟩).1 =
                      (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0) := by
                    funext k
                    have hk : k.val = 0 := by
                      have := k.isLt
                      omega
                    have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
                    rw [ek]
                    rfl
                  have e2 : (f.toFun ⟨fun _ => b, hb⟩).1 =
                      (fun _ : Fin 1 => (f.toFun ⟨fun _ => b, hb⟩).1 0) := by
                    funext k
                    have hk : k.val = 0 := by
                      have := k.isLt
                      omega
                    have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
                    rw [ek]
                    rfl
                  rw [e1, e2, h0]
                obtain ⟨c0, hsc0, hc0d, hc0m⟩ := hBetween2U sL dsC m hsdC' hslm
                have hcsCc0 : LT.lt csC c0 := lt_trans hcsC' hsc0
                obtain ⟨u2, hsu2, hcu2, hu2c0⟩ := hBetween3U sL csC c0 hsc0 hcsCc0
                obtain ⟨u1, hsu1, hcu1, hu1u2⟩ := hBetween3U sL csC u2 hsu2 hcu2
                have hu1m : LT.lt u1 m := lt_trans hu1u2 (lt_trans hu2c0 hc0m)
                have hu2m : LT.lt u2 m := lt_trans hu2c0 hc0m
                have hu1hi : LT.lt u1 hi := lt_trans hu1m hm_hi
                have hu2hi : LT.lt u2 hi := lt_trans hu2m hm_hi
                have hJ1 : openInterval (Endpoint.finite lo)
                    (Endpoint.finite hi) (fun _ => u1) :=
                  ⟨lt_trans hlt hsu1, hu1hi⟩
                have hJ2 : openInterval (Endpoint.finite lo)
                    (Endpoint.finite hi) (fun _ => u2) :=
                  ⟨lt_trans hlt hsu2, hu2hi⟩
                have hI1 : I (fun _ => u1) := (hIcon _ hJ1).2
                have hI2 : I (fun _ => u2) := (hIcon _ hJ2).2
                have eC := hEqCU u1 u2 hI1 hI2 hcu1
                  (lt_trans hu1u2 (lt_trans hu2c0 hc0d)) hcu2 (lt_trans hu2c0 hc0d)
                obtain ⟨t1, ht1S, htt1⟩ := hExceedLU u1 hsu1
                have eI := hEqSLU t1 ht1S u1 u2 hI1 hI2 htt1 hu1m
                  (lt_trans htt1 hu1u2) hu2m hu1u2
                have eIR : LT.lt ((f.toFun ⟨fun _ => u1, hI1⟩).1 0)
                    ((f.toFun ⟨fun _ => u2, hI2⟩).1 0) := eI
                have h0 := congrArg (· 0) eC
                rw [h0] at eIR
                exact lt_irrefl _ eIR
              · -- U window at sL: increasing extends left past sL.
                obtain ⟨-, -, csU, dsU, hcsU, hsdU, hNBU⟩ := hUs
                have hcsU' : LT.lt csU sL := hcsU
                have hsdU' : LT.lt sL dsU := hsdU
                obtain ⟨t', hct', hlot', ht'sL⟩ := hBetween3U csU lo sL hcsU' hlt
                have hIncTL : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                    LT.lt t' a → LT.lt a m → LT.lt t' b → LT.lt b m → LT.lt a b →
                    Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
                  intro a b ha hb hta ham htb hbm hab
                  rcases lt_trichotomy b sL with h | h | h
                  · have hlt_bs := h
                    exact hEqWinUG csU dsU hNBU a b ha hb
                      (lt_trans hct' hta) (lt_trans (lt_trans hab hlt_bs) hsdU')
                      (lt_trans hct' htb) (lt_trans hlt_bs hsdU') hab
                  · have heq_bs := h
                    have has : LT.lt a sL := by
                      rw [← heq_bs]
                      exact hab
                    have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) =
                        ⟨fun _ => sL, hIsLI⟩ :=
                      Subtype.ext (by funext k; exact heq_bs)
                    rw [ept]
                    obtain ⟨w, haw, hwcs, hws⟩ := hBetween3U a csU sL has hcsU'
                    have hJw : openInterval (Endpoint.finite lo)
                        (Endpoint.finite hi) (fun _ => w) :=
                      ⟨lt_trans hlot' (lt_trans hta haw), lt_trans hws (lt_trans hslm hm_hi)⟩
                    have hwI : I (fun _ => w) := (hIcon _ hJw).2
                    have e1 := hEqWinUG csU dsU hNBU a w ha hwI
                      (lt_trans hct' hta) (lt_trans haw (lt_trans hws hsdU'))
                      (lt_trans (lt_trans hct' hta) haw) (lt_trans hws hsdU') haw
                    have e2 := hEqWinUG csU dsU hNBU w sL hwI hIsLI hwcs
                      (lt_trans hws hsdU') hcsU' hsdU' hws
                    exact lt_trans e1 e2
                  · have hlt_sb := h
                    rcases lt_trichotomy a sL with h2 | h2 | h2
                    · have hlt_as := h2
                      have e1 := hEqWinUG csU dsU hNBU a sL ha hIsLI
                        (lt_trans hct' hta) (lt_trans hlt_as hsdU')
                        hcsU' hsdU' hlt_as
                      obtain ⟨w, hsw, hwb, hwds⟩ := hBetween2U sL b dsU hlt_sb hsdU'
                      have hJw : openInterval (Endpoint.finite lo)
                          (Endpoint.finite hi) (fun _ => w) :=
                        ⟨lt_trans hlt hsw, lt_trans hwb (lt_trans hbm hm_hi)⟩
                      have hwI : I (fun _ => w) := (hIcon _ hJw).2
                      have e2a := hEqWinUG csU dsU hNBU sL w hIsLI hwI
                        hcsU' hsdU' (lt_trans hcsU' hsw) hwds hsw
                      obtain ⟨t1, ht1S, hwt1⟩ := hExceedLU w hsw
                      have e2b := hEqSLU t1 ht1S w b hwI hb
                        hwt1 (lt_trans hwb hbm) (lt_trans hwt1 hwb) hbm hwb
                      exact lt_trans e1 (lt_trans e2a e2b)
                    · have heq_as := h2
                      have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) =
                          ⟨fun _ => sL, hIsLI⟩ :=
                        Subtype.ext (by funext k; exact heq_as)
                      rw [ept]
                      obtain ⟨w, hsw, hwb, hwds⟩ := hBetween2U sL b dsU hlt_sb hsdU'
                      have hJw : openInterval (Endpoint.finite lo)
                          (Endpoint.finite hi) (fun _ => w) :=
                        ⟨lt_trans hlt hsw, lt_trans hwb (lt_trans hbm hm_hi)⟩
                      have hwI : I (fun _ => w) := (hIcon _ hJw).2
                      have e1 := hEqWinUG csU dsU hNBU sL w hIsLI hwI
                        hcsU' hsdU' (lt_trans hcsU' hsw) hwds hsw
                      obtain ⟨t1, ht1S, hwt1⟩ := hExceedLU w hsw
                      have e2 := hEqSLU t1 ht1S w b hwI hb
                        hwt1 (lt_trans hwb hbm) (lt_trans hwt1 hwb) hbm hwb
                      exact lt_trans e1 e2
                    · have hlt_sa := h2
                      obtain ⟨t1, ht1S, htt1⟩ := hExceedLU a hlt_sa
                      exact hEqSLU t1 ht1S a b ha hb htt1 ham
                        (lt_trans htt1 hab) hbm hab
                have hT'LU : SLU (fun _ => t') := by
                  refine ⟨⟨?_, ?_⟩, lt_trans ht'sL hslm, ?_⟩
                  · rcases hlo_ac with heq2 | hlt2
                    · rw [← heq2]
                      exact hlot'
                    · exact lt_trans hlt2 hlot'
                  · exact lt_trans ht'sL (lt_trans hslm (hJ₀m.right))
                  · intro hex
                    obtain ⟨a, b, wpc, wqc, hIp, hIq, hJp, hJq,
                      hta, ham, htb, hbm, hLT, hGp, hGq, hbadU⟩ := hex
                    have hLt := hIncTL a b hIp hIq hta ham htb hbm hLT
                    have hLtR : LT.lt ((f.toFun ⟨fun _ => a, hIp⟩).1 0)
                        ((f.toFun ⟨fun _ => b, hIq⟩).1 0) := hLt
                    have hwpc := wpcEqVal f a wpc hIp hGp
                    have hwqc := wpcEqVal f b wqc hIq hGq
                    rw [hwpc, hwqc] at hbadU
                    rcases hbadU with h1 | h2
                    · exact lt_irrefl _ (lt_trans hLtR h1)
                    · have hr : ((f.toFun ⟨fun _ => a, hIp⟩).1 0) =
                          ((f.toFun ⟨fun _ => b, hIq⟩).1 0) :=
                        congrArg (· 0) h2
                      rw [hr] at hLtR
                      exact lt_irrefl _ hLtR
                have ht'SLU' : SLU' (fun _ => t') := ⟨hT'LU, ⟨hlot', lt_trans ht'sL hslm⟩⟩
                rcases hsInf.1 (fun _ => t') ht'SLU' with h | h
                · exact lt_irrefl _ (lt_trans h ht'sL)
                · rw [← h] at ht'sL
                  exact lt_irrefl _ ht'sL
              · -- Dc window at sL meets approached increase: contradiction.
                obtain ⟨-, -, csD, dsD, hcsD, hsdD, hNBD⟩ := hDs
                have hcsD' : LT.lt csD sL := hcsD
                have hsdD' : LT.lt sL dsD := hsdD
                have hEqWinDUD : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                    LT.lt csD a → LT.lt a dsD → LT.lt csD b → LT.lt b dsD → LT.lt a b →
                    Lt1 (f.toFun ⟨fun _ => b, hb⟩).1 (f.toFun ⟨fun _ => a, ha⟩).1 := by
                  intro a b ha hb hau hav hbu hbv hab
                  rcases lt_trichotomy ((f.toFun ⟨fun _ => a, ha⟩).1 0)
                      ((f.toFun ⟨fun _ => b, hb⟩).1 0) with h | h | h
                  · have hlt := h
                    exfalso
                    apply hNBD
                    refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                      (f.toFun ⟨fun _ => b, hb⟩).1 0,
                      ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                      graphAppendConst f a ha, graphAppendConst f b hb, Or.inl ?_⟩
                    exact hlt
                  · have heq := h
                    exfalso
                    apply hNBD
                    refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
                      (f.toFun ⟨fun _ => b, hb⟩).1 0,
                      ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩, hab,
                      graphAppendConst f a ha, graphAppendConst f b hb, Or.inr ?_⟩
                    exact congrArg (fun w : R => (fun _ : Fin 1 => w)) heq
                  · have hlt := h
                    exact hlt
                obtain ⟨c0, hsc0, hc0d, hc0m⟩ := hBetween2U sL dsD m hsdD' hslm
                have hcsDc0 : LT.lt csD c0 := lt_trans hcsD' hsc0
                obtain ⟨u2, hsu2, hcu2, hu2c0⟩ := hBetween3U sL csD c0 hsc0 hcsDc0
                obtain ⟨u1, hsu1, hcu1, hu1u2⟩ := hBetween3U sL csD u2 hsu2 hcu2
                have hu1m : LT.lt u1 m := lt_trans hu1u2 (lt_trans hu2c0 hc0m)
                have hu2m : LT.lt u2 m := lt_trans hu2c0 hc0m
                have hu1hi : LT.lt u1 hi := lt_trans hu1m hm_hi
                have hu2hi : LT.lt u2 hi := lt_trans hu2m hm_hi
                have hJ1 : openInterval (Endpoint.finite lo)
                    (Endpoint.finite hi) (fun _ => u1) :=
                  ⟨lt_trans hlt hsu1, hu1hi⟩
                have hJ2 : openInterval (Endpoint.finite lo)
                    (Endpoint.finite hi) (fun _ => u2) :=
                  ⟨lt_trans hlt hsu2, hu2hi⟩
                have hI1 : I (fun _ => u1) := (hIcon _ hJ1).2
                have hI2 : I (fun _ => u2) := (hIcon _ hJ2).2
                obtain ⟨t1, ht1S, htt1⟩ := hExceedLU u1 hsu1
                have eI := hEqSLU t1 ht1S u1 u2 hI1 hI2 htt1 hu1m
                  (lt_trans htt1 hu1u2) hu2m hu1u2
                have eD := hEqWinDUD u1 u2 hI1 hI2 hcu1
                  (lt_trans hu1u2 (lt_trans hu2c0 hc0d)) hcu2 (lt_trans hu2c0 hc0d) hu1u2
                have eIR : LT.lt ((f.toFun ⟨fun _ => u1, hI1⟩).1 0)
                    ((f.toFun ⟨fun _ => u2, hI2⟩).1 0) := eI
                have eDR : LT.lt ((f.toFun ⟨fun _ => u2, hI2⟩).1 0)
                    ((f.toFun ⟨fun _ => u1, hI1⟩).1 0) := eD
                exact lt_irrefl _ (lt_trans eIR eDR)
            · subst heq
              have hAnchorLU : ∀ a : R, ∀ (ha : I (fun _ => a)), LT.lt lo a → LT.lt a m →
                  Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨xm, hImm⟩).1 := by
                intro a ha hlo_a ham
                obtain ⟨b₀, hab₀, hub₀, hb₀m⟩ := hBetween3U a u₀ m ham hmu₀
                have hb₀v : LT.lt b₀ v₀ := lt_trans hb₀m hmv₀
                have hb₀I : I (fun _ => b₀) := by
                  have hJ : openInterval (Endpoint.finite lo)
                      (Endpoint.finite hi) (fun _ => b₀) :=
                    ⟨lt_trans hlo_a hab₀, lt_trans hb₀m hm_hi⟩
                  exact (hIcon _ hJ).2
                obtain ⟨t₁, ht₁S, htt₁⟩ := hExceedLU a hlo_a
                have e1 := hEqSLU t₁ ht₁S a b₀ ha hb₀I htt₁ ham
                  (lt_trans htt₁ hab₀) hb₀m hab₀
                have e2 := hEqWinUG u₀ v₀ hNBu₀ b₀ m hb₀I hImm hub₀ hb₀v
                  hmu₀ hmv₀ hb₀m
                exact lt_trans e1 e2
              have hIncR : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                  LT.lt lo a → LT.lt a hi → LT.lt lo b → LT.lt b hi → LT.lt a b →
                  Lt1 (f.toFun ⟨fun _ => a, ha⟩).1 (f.toFun ⟨fun _ => b, hb⟩).1 := by
                intro a b ha hb hlo_a hahi hlo_b hbhi hab
                rcases lt_trichotomy b m with h | h | h
                · have hlt_bm := h
                  obtain ⟨t₁, ht₁S, htt₁⟩ := hExceedLU a hlo_a
                  exact hEqSLU t₁ ht₁S a b ha hb htt₁ (lt_trans hab hlt_bm)
                    (lt_trans htt₁ hab) hlt_bm hab
                · have heq_bm := h
                  have ham : LT.lt a m := by
                    rw [← heq_bm]
                    exact hab
                  have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) = ⟨xm, hImm⟩ :=
                    Subtype.ext (congrArg (fun r : R => (fun _ : Fin 1 => r)) heq_bm)
                  rw [ept]
                  exact hAnchorLU a ha hlo_a ham
                · have hlt_mb := h
                  rcases lt_trichotomy a m with h2 | h2 | h2
                  · have hlt_am := h2
                    exact lt_trans (hAnchorLU a ha hlo_a hlt_am) (hAnchorRU b hb hlt_mb hbhi)
                  · have heq_am := h2
                    have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) = ⟨xm, hImm⟩ :=
                      Subtype.ext (congrArg (fun r : R => (fun _ : Fin 1 => r)) heq_am)
                    rw [ept]
                    exact hAnchorRU b hb hlt_mb hbhi
                  · have hlt_ma := h2
                    obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceedU b hbhi
                    exact hEqSU t₁ ht₁S a b ha hb hlt_ma (lt_trans hab hbt₁)
                      (lt_trans hlt_ma hab) hbt₁ hab
              refine Or.inr ⟨Or.inl ?_, ?_⟩
              · intro x hxI hJx y hyI hJy hlt
                have hxI2 : I (fun _ => Power.coord1 x) := by
                  rw [← ptLam x]
                  exact hxI
                have hyI2 : I (fun _ => Power.coord1 y) := by
                  rw [← ptLam y]
                  exact hyI
                have hJx2 : openInterval (Endpoint.finite lo) (Endpoint.finite hi)
                    (fun _ => Power.coord1 x) := by
                  rw [ptLam x] at hJx
                  exact hJx
                have hJy2 : openInterval (Endpoint.finite lo) (Endpoint.finite hi)
                    (fun _ => Power.coord1 y) := by
                  rw [ptLam y] at hJy
                  exact hJy
                have hlt' : LT.lt (Power.coord1 x) (Power.coord1 y) := hlt
                have eX : (⟨x, hxI⟩ : {x : Power R 1 // I x}) =
                    ⟨fun _ => Power.coord1 x, hxI2⟩ := Subtype.ext (ptLam x)
                have eY : (⟨y, hyI⟩ : {x : Power R 1 // I x}) =
                    ⟨fun _ => Power.coord1 y, hyI2⟩ := Subtype.ext (ptLam y)
                rw [eX, eY]
                exact hIncR _ _ _ _ hJx2.left hJx2.right hJy2.left hJy2.right hlt'
              · -- Continuity: no Disc point lies strictly inside the piece.
                intro x hJx
                have hxI : I x := (hIcon x hJx).2
                by_contra hNC
                obtain ⟨t, hWt⟩ :=
                   Monotonicity_Theorem.disc_witness_aux M f x hxI hNC
                have hmem : Power.coord1 x ∈ DiscList := hDiscListMp x ⟨t, hWt⟩
                have hE : Power.coord1 x ∈ E := hDisc'E _ hmem
                exact hconsec _ hE ⟨hJx.left, hJx.right⟩
      · -- Case C: const covers the piece.
        obtain ⟨m, hm_lo, hm_hi⟩ := exists_between hlohi
        set xm : Power R 1 := fun _ => m with hxmdef
        have hJm : openInterval (Endpoint.finite lo) (Endpoint.finite hi) xm :=
          ⟨hm_lo, hm_hi⟩
        obtain ⟨hJ₀m, hImm, u₀, v₀, hu₀, hv₀, hNB₀⟩ := hCcon xm hJm
        have hmu₀ : LT.lt u₀ m := hu₀
        have hmv₀ : LT.lt m v₀ := hv₀
        -- Equality from a const-violation-free window.
        have hEqWin : ∀ u v : R,
            (¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
              openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => pc) ∧
              openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => qc) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ => pc) (fun _ => wpc)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ => qc) (fun _ => wqc)) ∧
              ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc))) →
            ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
            LT.lt u a → LT.lt a v → LT.lt u b → LT.lt b v → LT.lt a b →
            (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
          intro u v hNBw a b ha hb hau hav hbu hbv hab
          by_contra hne
          apply hNBw
          refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
            (f.toFun ⟨fun _ => b, hb⟩).1 0,
            ha, hb, ⟨hau, hav⟩, ⟨hbu, hbv⟩,
            graphAppendConst f a ha, graphAppendConst f b hb, ?_⟩
          intro heq
          apply hne
          have h0 : (f.toFun ⟨fun _ => a, ha⟩).1 0 =
              (f.toFun ⟨fun _ => b, hb⟩).1 0 :=
            congrFun heq ⟨0, by decide⟩
          have e1 : (f.toFun ⟨fun _ => a, ha⟩).1 =
              (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0) := by
            funext k
            have hk : k.val = 0 := by
              have := k.isLt
              omega
            have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
            rw [ek]
            rfl
          have e2 : (f.toFun ⟨fun _ => b, hb⟩).1 =
              (fun _ : Fin 1 => (f.toFun ⟨fun _ => b, hb⟩).1 0) := by
            funext k
            have hk : k.val = 0 := by
              have := k.isLt
              omega
            have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
            rw [ek]
            rfl
          rw [e1, e2, h0]
        -- Right const-prefix set at m.
        set Sc : Set (Power R 1) := fun c : Power R 1 =>
          openInterval (Endpoint.finite ac) (Endpoint.finite bc) c ∧
          LT.lt m (Power.coord1 c) ∧
          ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
            openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => pc) ∧
            openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => qc) ∧
            LT.lt m pc ∧ LT.lt pc (Power.coord1 c) ∧
            LT.lt m qc ∧ LT.lt qc (Power.coord1 c) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => pc) (fun _ => wpc)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append (fun _ => qc) (fun _ => wqc)) ∧
            ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)) with hScdef
        have hScmem : M.S 1 Sc := constPrefixRDefinable M f ac bc m
        -- Equality on a const-prefix segment.
        have hEqS : ∀ t : R, Sc (fun _ => t) → ∀ a b : R,
            ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
            LT.lt m a → LT.lt a t → LT.lt m b → LT.lt b t → LT.lt a b →
            (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
          intro t hT a b ha hb hma hat hmb hbt hab
          obtain ⟨hJt, hmt, hNV⟩ := hT
          have hta : LT.lt t bc := hJt.right
          have hac_a : LT.lt ac a := by
            rcases hlo_ac with heq | hlt
            · rw [← heq]
              exact lt_trans hm_lo hma
            · exact lt_trans hlt (lt_trans hm_lo hma)
          have hac_b : LT.lt ac b := by
            rcases hlo_ac with heq | hlt
            · rw [← heq]
              exact lt_trans hm_lo hmb
            · exact lt_trans hlt (lt_trans hm_lo hmb)
          by_contra hne
          apply hNV
          refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
            (f.toFun ⟨fun _ => b, hb⟩).1 0,
            ha, hb, ⟨hac_a, lt_trans hat hta⟩, ⟨hac_b, lt_trans hbt hta⟩,
            hma, hat, hmb, hbt,
            graphAppendConst f a ha, graphAppendConst f b hb, ?_⟩
          intro heq
          apply hne
          have h0 : (f.toFun ⟨fun _ => a, ha⟩).1 0 =
              (f.toFun ⟨fun _ => b, hb⟩).1 0 :=
            congrFun heq ⟨0, by decide⟩
          have e1 : (f.toFun ⟨fun _ => a, ha⟩).1 =
              (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0) := by
            funext k
            have hk : k.val = 0 := by
              have := k.isLt
              omega
            have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
            rw [ek]
            rfl
          have e2 : (f.toFun ⟨fun _ => b, hb⟩).1 =
              (fun _ : Fin 1 => (f.toFun ⟨fun _ => b, hb⟩).1 0) := by
            funext k
            have hk : k.val = 0 := by
              have := k.isLt
              omega
            have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
            rw [ek]
            rfl
          rw [e1, e2, h0]
        -- A point below two upper bounds.
        have hmin2 : ∀ p q : R, LT.lt m p → LT.lt m q →
            ∃ t, LT.lt m t ∧ LT.lt t p ∧ LT.lt t q := by
          intro p q hmp hmq
          rcases lt_trichotomy p q with h | h | h
          · have hlt := h
            obtain ⟨t, hmt, htp⟩ := exists_between hmp
            exact ⟨t, hmt, htp, lt_trans htp hlt⟩
          · have heq := h
            obtain ⟨t, hmt, htp⟩ := exists_between hmp
            rw [heq] at htp ⊢
            exact ⟨t, hmt, htp, htp⟩
          · have hlt := h
            obtain ⟨t, hmt, htq⟩ := exists_between hmq
            exact ⟨t, hmt, lt_trans htq hlt, htq⟩
        -- The bounded prefix set.
        set S' : Set (Power R 1) := Sc ∩
          (openInterval (Endpoint.finite m) (Endpoint.finite hi)) with hS'def
        have hS'mem : M.S 1 S' :=
          M.inter_mem hScmem
            ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _))
        have hS'ne : S'.Nonempty := by
          obtain ⟨t₁, hm1, h1v, h1h⟩ := hmin2 v₀ hi hmv₀ hm_hi
          obtain ⟨t, hmt, ht1, hbc⟩ := hmin2 t₁ bc hm1 hJ₀m.right
          have htv₀ : LT.lt t v₀ := lt_trans ht1 h1v
          have hthi : LT.lt t hi := lt_trans ht1 h1h
          refine ⟨fun _ => t, ?_, ?_⟩
          · -- t ∈ Sc: window gives no violation on [m,t).
            refine ⟨⟨?_, ?_⟩, hmt, ?_⟩
            · rcases hlo_ac with heq | hlt
              · rw [← heq]
                exact lt_trans hm_lo hmt
              · exact lt_trans hlt (lt_trans hm_lo hmt)
            · exact hbc
            · intro hex
              apply hNB₀
              obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq,
                hmpc, hpc_t, hmqc, hqc_t, hGp, hGq, hne⟩ := hex
              refine ⟨pc, qc, wpc, wqc, hIp, hIq, ?_, ?_, hGp, hGq, hne⟩
              · exact ⟨lt_trans hmu₀ hmpc, lt_trans hpc_t htv₀⟩
              · exact ⟨lt_trans hmu₀ hmqc, lt_trans hqc_t htv₀⟩
          · exact ⟨hmt, hthi⟩
        -- Points are determined by coordinates.
        have hPtLam : ∀ x : Power R 1, x = fun _ => Power.coord1 x := by
          intro x
          funext k
          have hk : k.val = 0 := by
            have := k.isLt
            omega
          have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
          rw [ek]
          rfl
        -- A point strictly below two upper bounds.
        have hBetween2 : ∀ z p q : R, LT.lt z p → LT.lt z q →
            ∃ w, LT.lt z w ∧ LT.lt w p ∧ LT.lt w q := by
          intro z p q hzp hzq
          rcases lt_trichotomy p q with h | h | h
          · have hlt := h
            obtain ⟨w, hzw, hwp⟩ := exists_between hzp
            exact ⟨w, hzw, hwp, lt_trans hwp hlt⟩
          · have heq := h
            obtain ⟨w, hzw, hwp⟩ := exists_between hzp
            rw [heq] at hwp ⊢
            exact ⟨w, hzw, hwp, hwp⟩
          · have hlt := h
            obtain ⟨w, hzw, hwq⟩ := exists_between hzq
            exact ⟨w, hzw, lt_trans hwq hlt, hwq⟩
        have hub_hi : IsUpperBound1 S' hi := by
          intro x hx
          obtain ⟨-, hJx⟩ := hx
          exact Or.inl hJx.right
        have hS'bd : BoundedAbove1 S' := ⟨hi, hub_hi⟩
        obtain ⟨s, hsSup⟩ := supCompletenessAux S'
          ((M.ominimal _).mp hS'mem) hS'ne hS'bd
        -- Exceeding any bound below the sup.
        have hExceed : ∀ b : R, LT.lt b s → ∃ t₁, Sc (fun _ => t₁) ∧ LT.lt b t₁ := by
          intro b hbs
          by_contra hcon
          push Not at hcon
          have hub : IsUpperBound1 S' b := by
            intro x hx
            obtain ⟨hScx, -⟩ := hx
            have e : x = fun _ => Power.coord1 x := hPtLam x
            rw [e] at hScx
            have hle : ¬ LT.lt b (Power.coord1 x) := not_lt_of_ge (hcon _ hScx)
            rcases lt_trichotomy (Power.coord1 x) b with h | h | h
            · have hlt := h
              exact Or.inl hlt
            · have heq := h
              exact Or.inr heq
            · have hlt := h
              exact False.elim (hle hlt)
          rcases hsSup.2 b hub with h | h
          · exact lt_irrefl _ (lt_trans hbs h)
          · rw [h] at hbs
            exact lt_irrefl _ hbs
        -- Below three bounds at once.
        have hBetween3 : ∀ z₁ z₂ p : R, LT.lt z₁ p → LT.lt z₂ p →
            ∃ w, LT.lt z₁ w ∧ LT.lt z₂ w ∧ LT.lt w p := by
          intro z₁ z₂ p h1 h2
          rcases lt_trichotomy z₁ z₂ with h | h | h
          · have hlt := h
            obtain ⟨w, hzw, hwp⟩ := exists_between h2
            exact ⟨w, lt_trans hlt hzw, hzw, hwp⟩
          · have heq := h
            obtain ⟨w, hzw, hwp⟩ := exists_between h2
            refine ⟨w, ?_, hzw, hwp⟩
            rw [heq]
            exact hzw
          · have hlt := h
            obtain ⟨w, hzw, hwp⟩ := exists_between h1
            exact ⟨w, hzw, lt_trans hlt hzw, hwp⟩
        rcases hsSup.2 hi hub_hi with hlt | heq
        · exfalso
          obtain ⟨t₀, ht₀⟩ := hS'ne
          obtain ⟨hJt₀, hmt₀, hNV₀⟩ := ht₀.1
          have hms : LT.lt m s := by
            rcases hsSup.1 t₀ ht₀ with h | h
            · exact lt_trans hmt₀ h
            · rw [← h]; exact hmt₀
          have hJs : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => s) :=
            ⟨lt_trans hm_lo hms, hlt⟩
          obtain ⟨hJ₀s, hIsI⟩ := hIcon _ hJs
          have hBs : C (fun _ => s) ∨ U (fun _ => s) ∨ Dc (fun _ => s) := by
            by_contra hcon
            apply hNB _ hJs
            rw [hBaddef]
            refine ⟨hIcon _ hJs, ?_⟩
            exact hcon
          rcases hBs with hCs | hUs | hDs
          · -- C window at s: const extends past s.
            obtain ⟨-, -, cs, ds, hcs, hsd, hNBs⟩ := hCs
            have hcs' : LT.lt cs s := hcs
            have hsd' : LT.lt s ds := hsd
            obtain ⟨t', ht's, ht'd, ht'h⟩ := hBetween2 s ds hi hsd' hlt
            have hT' : Sc (fun _ => t') := by
              refine ⟨⟨?_, ?_⟩, lt_trans hms ht's, ?_⟩
              · rcases hlo_ac with heq2 | hlt2
                · rw [← heq2]
                  exact lt_trans hm_lo (lt_trans hms ht's)
                · exact lt_trans hlt2 (lt_trans hm_lo (lt_trans hms ht's))
              · rcases hhi_bc with heq2 | hlt2
                · rw [← heq2]
                  exact ht'h
                · exact lt_trans ht'h hlt2
              · -- Const on [m, t'].
                have hCt' : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                    LT.lt m a → LT.lt a t' → LT.lt m b → LT.lt b t' → LT.lt a b →
                    (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
                  intro a b ha hb hma hat hmb hbt hab
                  rcases lt_trichotomy b s with h | h | h
                  · have hlt_bs := h
                    obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceed b hlt_bs
                    exact hEqS t₁ ht₁S a b ha hb hma
                      (lt_trans hab hbt₁) hmb hbt₁ hab
                  · have heq_bs := h
                    obtain ⟨w, haw, hwcs, hws⟩ := hBetween3 a cs s
                      (by rw [← heq_bs]; exact hab) hcs'
                    have hmw : LT.lt m w := lt_trans hma haw
                    have hwhi : LT.lt w hi := lt_trans hws hlt
                    have hJw : openInterval (Endpoint.finite lo)
                        (Endpoint.finite hi) (fun _ => w) :=
                      ⟨lt_trans hm_lo hmw, hwhi⟩
                    have hwI : I (fun _ => w) := (hIcon _ hJw).2
                    obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceed w hws
                    have e1 := hEqS t₁ ht₁S a w ha hwI hma
                      (lt_trans haw hwt₁) (lt_trans hma haw) hwt₁ haw
                    have e2 := hEqWin cs ds hNBs w s hwI hIsI hwcs
                      (lt_trans hws hsd') hcs' hsd' hws
                    have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) =
                        ⟨fun _ => s, hIsI⟩ := Subtype.ext (by funext k; exact heq_bs)
                    rw [ept]
                    exact Eq.trans e1 e2
                  · have hlt_sb := h
                    rcases lt_trichotomy a s with h2 | h2 | h2
                    · have hlt_as := h2
                      obtain ⟨w, haw, hwcs, hws⟩ := hBetween3 a cs s hlt_as hcs'
                      have hmw : LT.lt m w := lt_trans hma haw
                      have hwhi : LT.lt w hi := lt_trans hws hlt
                      have hJw : openInterval (Endpoint.finite lo)
                          (Endpoint.finite hi) (fun _ => w) :=
                        ⟨lt_trans hm_lo hmw, hwhi⟩
                      have hwI : I (fun _ => w) := (hIcon _ hJw).2
                      obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceed w hws
                      have e1 := hEqS t₁ ht₁S a w ha hwI hma
                        (lt_trans haw hwt₁) (lt_trans hma haw) hwt₁ haw
                      have e2 := hEqWin cs ds hNBs w b hwI hb hwcs
                        (lt_trans hws (lt_trans hlt_sb (lt_trans hbt ht'd)))
                        (lt_trans hcs' hlt_sb) (lt_trans hbt ht'd)
                        (lt_trans hws hlt_sb)
                      exact Eq.trans e1 e2
                    · have heq_as := h2
                      have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) =
                          ⟨fun _ => s, hIsI⟩ := Subtype.ext (by funext k; exact heq_as)
                      rw [ept]
                      exact hEqWin cs ds hNBs s b hIsI hb hcs' hsd'
                        (lt_trans hcs' hlt_sb) (lt_trans hbt ht'd) hlt_sb
                    · have hlt_sa := h2
                      exact hEqWin cs ds hNBs a b ha hb
                        (lt_trans hcs' hlt_sa) (lt_trans hat ht'd)
                        (lt_trans (lt_trans hcs' hlt_sa) hab) (lt_trans hbt ht'd) hab
                intro hex
                obtain ⟨a, b, wpc, wqc, hIp, hIq, hJp, hJq,
                  hmpc, hpc_t, hmqc, hqc_t, hGp, hGq, hne⟩ := hex
                rcases lt_trichotomy a b with hab | hab | hab
                · have hlt_ab := hab
                  have heqAB := hCt' a b hIp hIq hmpc hpc_t hmqc hqc_t hlt_ab
                  have hwpc := wpcEqVal f a wpc hIp hGp
                  have hwqc := wpcEqVal f b wqc hIq hGq
                  have hr : wpc = wqc := hwpc.trans
                    ((congrArg (· 0) heqAB).trans hwqc.symm)
                  exact hne (congrArg (fun w : R => (fun _ : Fin 1 => w)) hr)
                · have heq_ab := hab
                  have ept : (⟨fun _ => b, hIq⟩ : {x : Power R 1 // I x}) =
                      ⟨fun _ => a, hIp⟩ := Subtype.ext
                    (congrArg (fun c : R => (fun _ : Fin 1 => c)) heq_ab.symm)
                  have hwpc := wpcEqVal f a wpc hIp hGp
                  have hwqc := wpcEqVal f b wqc hIq hGq
                  rw [ept] at hwqc
                  rw [hwpc, hwqc] at hne
                  exact False.elim (hne rfl)
                · have hlt_ba := hab
                  have heqAB := hCt' b a hIq hIp hmqc hqc_t hmpc hpc_t hlt_ba
                  have hwpc := wpcEqVal f a wpc hIp hGp
                  have hwqc := wpcEqVal f b wqc hIq hGq
                  have hr : wpc = wqc := hwpc.trans
                    ((congrArg (· 0) heqAB.symm).trans hwqc.symm)
                  exact hne (congrArg (fun w : R => (fun _ : Fin 1 => w)) hr)
            have ht'S : S' (fun _ => t') := ⟨hT', ⟨lt_trans hms ht's, ht'h⟩⟩
            rcases hsSup.1 (fun _ => t') ht'S with h | h
            · exact lt_irrefl _ (lt_trans ht's h)
            · rw [← h] at ht's
              exact lt_irrefl _ ht's
          · -- U window at s contradicts approached const.
            obtain ⟨-, -, cs, ds, hcs, hsd, hNBu⟩ := hUs
            have hcs' : LT.lt cs s := hcs
            have hsd' : LT.lt s ds := hsd
            obtain ⟨z, hmz, hcz, hzs⟩ := hBetween3 m cs s hms hcs'
            obtain ⟨u₁, hzu₁, hu₁s⟩ := exists_between hzs
            obtain ⟨u₂, h1u₂, hu₂s⟩ := exists_between hu₁s
            have hmz₁ : LT.lt m u₁ := lt_trans hmz hzu₁
            have hmz₂ : LT.lt m u₂ := lt_trans hmz (lt_trans hzu₁ h1u₂)
            have hu₁hi : LT.lt u₁ hi := lt_trans hu₁s hlt
            have hu₂hi : LT.lt u₂ hi := lt_trans hu₂s hlt
            have hJ₁ : openInterval (Endpoint.finite lo)
                (Endpoint.finite hi) (fun _ => u₁) :=
              ⟨lt_trans hm_lo hmz₁, hu₁hi⟩
            have hJ₂ : openInterval (Endpoint.finite lo)
                (Endpoint.finite hi) (fun _ => u₂) :=
              ⟨lt_trans hm_lo hmz₂, hu₂hi⟩
            have hI₁ : I (fun _ => u₁) := (hIcon _ hJ₁).2
            have hI₂ : I (fun _ => u₂) := (hIcon _ hJ₂).2
            obtain ⟨t₁, ht₁S, hu₂t₁⟩ := hExceed u₂ hu₂s
            have heq12 := hEqS t₁ ht₁S u₁ u₂ hI₁ hI₂
              (lt_trans hmz hzu₁) (lt_trans h1u₂ hu₂t₁)
              (lt_trans hmz (lt_trans hzu₁ h1u₂)) hu₂t₁ h1u₂
            have hw12 : (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0 =
                (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0 :=
              congrArg (· 0) heq12
            apply hNBu
            refine ⟨u₁, u₂, (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0,
              (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0,
              hI₁, hI₂, ⟨lt_trans hcz hzu₁, lt_trans hu₁s hsd'⟩,
              ⟨lt_trans hcz (lt_trans hzu₁ h1u₂), lt_trans hu₂s hsd'⟩,
              h1u₂, graphAppendConst f _ hI₁, graphAppendConst f _ hI₂,
              Or.inr ?_⟩
            show (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0) =
              (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0)
            exact congrArg (fun w => (fun _ : Fin 1 => w)) hw12
          · -- Dc window at s contradicts approached const.
            obtain ⟨-, -, cs, ds, hcs, hsd, hNBd⟩ := hDs
            have hcs' : LT.lt cs s := hcs
            have hsd' : LT.lt s ds := hsd
            obtain ⟨z, hmz, hcz, hzs⟩ := hBetween3 m cs s hms hcs'
            obtain ⟨u₁, hzu₁, hu₁s⟩ := exists_between hzs
            obtain ⟨u₂, h1u₂, hu₂s⟩ := exists_between hu₁s
            have hmz₁ : LT.lt m u₁ := lt_trans hmz hzu₁
            have hmz₂ : LT.lt m u₂ := lt_trans hmz (lt_trans hzu₁ h1u₂)
            have hu₁hi : LT.lt u₁ hi := lt_trans hu₁s hlt
            have hu₂hi : LT.lt u₂ hi := lt_trans hu₂s hlt
            have hJ₁ : openInterval (Endpoint.finite lo)
                (Endpoint.finite hi) (fun _ => u₁) :=
              ⟨lt_trans hm_lo hmz₁, hu₁hi⟩
            have hJ₂ : openInterval (Endpoint.finite lo)
                (Endpoint.finite hi) (fun _ => u₂) :=
              ⟨lt_trans hm_lo hmz₂, hu₂hi⟩
            have hI₁ : I (fun _ => u₁) := (hIcon _ hJ₁).2
            have hI₂ : I (fun _ => u₂) := (hIcon _ hJ₂).2
            obtain ⟨t₁, ht₁S, hu₂t₁⟩ := hExceed u₂ hu₂s
            have heq12 := hEqS t₁ ht₁S u₁ u₂ hI₁ hI₂
              (lt_trans hmz hzu₁) (lt_trans h1u₂ hu₂t₁)
              (lt_trans hmz (lt_trans hzu₁ h1u₂)) hu₂t₁ h1u₂
            have hw12 : (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0 =
                (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0 :=
              congrArg (· 0) heq12
            apply hNBd
            refine ⟨u₁, u₂, (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0,
              (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0,
              hI₁, hI₂, ⟨lt_trans hcz hzu₁, lt_trans hu₁s hsd'⟩,
              ⟨lt_trans hcz (lt_trans hzu₁ h1u₂), lt_trans hu₂s hsd'⟩,
              h1u₂, graphAppendConst f _ hI₁, graphAppendConst f _ hI₂,
              Or.inr ?_⟩
            show (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0) =
              (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0)
            exact congrArg (fun w => (fun _ : Fin 1 => w)) hw12
        · subst heq
          have hAnchorR : ∀ b : R, ∀ (hb : I (fun _ => b)), LT.lt m b → LT.lt b hi →
              (f.toFun ⟨fun _ => b, hb⟩).1 = (f.toFun ⟨xm, hImm⟩).1 := by
            intro b hb hmb hbhi
            obtain ⟨t₁, ht₁S, hbt₁⟩ := hExceed b hbhi
            obtain ⟨a₀, hma₀, ha₀b, ha₀v⟩ := hBetween2 m b v₀ hmb hmv₀
            have ha₀I : I (fun _ => a₀) := by
              have hJ : openInterval (Endpoint.finite lo)
                  (Endpoint.finite hi) (fun _ => a₀) :=
                ⟨lt_trans hm_lo hma₀, lt_trans ha₀b hbhi⟩
              exact (hIcon _ hJ).2
            have e1 := hEqWin u₀ v₀ hNB₀ m a₀ hImm ha₀I hmu₀ hmv₀
              (lt_trans hmu₀ hma₀) ha₀v hma₀
            have e2 := hEqS t₁ ht₁S a₀ b ha₀I hb
              hma₀ (lt_trans ha₀b hbt₁) hmb hbt₁ ha₀b
            exact (Eq.trans e1 e2).symm
          -- Left const-prefix set at m.
          set SL : Set (Power R 1) := fun c : Power R 1 =>
            openInterval (Endpoint.finite ac) (Endpoint.finite bc) c ∧
            LT.lt (Power.coord1 c) m ∧
            ¬ ∃ pc qc wpc wqc : R, I (fun _ => pc) ∧ I (fun _ => qc) ∧
              openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => pc) ∧
              openInterval (Endpoint.finite ac) (Endpoint.finite bc) (fun _ => qc) ∧
              LT.lt (Power.coord1 c) pc ∧ LT.lt pc m ∧
              LT.lt (Power.coord1 c) qc ∧ LT.lt qc m ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ => pc) (fun _ => wpc)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ => qc) (fun _ => wqc)) ∧
              ¬ ((fun _ : Fin 1 => wpc) = (fun _ : Fin 1 => wqc)) with hSLdef
          have hSLmem : M.S 1 SL := constPrefixLDefinable M f ac bc m
          have hEqSL : ∀ t : R, SL (fun _ => t) → ∀ a b : R,
              ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
              LT.lt t a → LT.lt a m → LT.lt t b → LT.lt b m → LT.lt a b →
              (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
            intro t hT a b ha hb hta ham htb hbm hab
            obtain ⟨hJt, htm, hNV⟩ := hT
            have hta2 : LT.lt t bc := hJt.right
            have hac_a : LT.lt ac a := lt_trans hJt.left hta
            have hac_b : LT.lt ac b := lt_trans hJt.left htb
            have hbc_a : LT.lt a bc := by
              have hmbc : LT.lt m bc := hJ₀m.right
              exact lt_trans ham hmbc
            have hbc_b : LT.lt b bc := by
              have hmbc : LT.lt m bc := hJ₀m.right
              exact lt_trans hbm hmbc
            by_contra hne
            apply hNV
            refine ⟨a, b, (f.toFun ⟨fun _ => a, ha⟩).1 0,
              (f.toFun ⟨fun _ => b, hb⟩).1 0,
              ha, hb, ⟨hac_a, hbc_a⟩, ⟨hac_b, hbc_b⟩,
              hta, ham, htb, hbm,
              graphAppendConst f a ha, graphAppendConst f b hb, ?_⟩
            intro heq
            apply hne
            have h0 : (f.toFun ⟨fun _ => a, ha⟩).1 0 =
                (f.toFun ⟨fun _ => b, hb⟩).1 0 :=
              congrFun heq ⟨0, by decide⟩
            have e1 : (f.toFun ⟨fun _ => a, ha⟩).1 =
                (fun _ : Fin 1 => (f.toFun ⟨fun _ => a, ha⟩).1 0) := by
              funext k
              have hk : k.val = 0 := by
                have := k.isLt
                omega
              have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
              rw [ek]
              rfl
            have e2 : (f.toFun ⟨fun _ => b, hb⟩).1 =
                (fun _ : Fin 1 => (f.toFun ⟨fun _ => b, hb⟩).1 0) := by
              funext k
              have hk : k.val = 0 := by
                have := k.isLt
                omega
              have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
              rw [ek]
              rfl
            rw [e1, e2, h0]
          -- Left bounded prefix set.
          set SL' : Set (Power R 1) := SL ∩
            (openInterval (Endpoint.finite lo) (Endpoint.finite m)) with hSL'def
          have hSL'mem : M.S 1 SL' :=
            M.inter_mem hSLmem
              ((M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _))
          have hSL'ne : SL'.Nonempty := by
            obtain ⟨t, hlot, htu₀, htm⟩ := hBetween3 lo u₀ m hm_lo hmu₀
            have htv₀ : LT.lt t v₀ := lt_trans htm hmv₀
            refine ⟨fun _ => t, ?_, ?_⟩
            · refine ⟨⟨?_, ?_⟩, htm, ?_⟩
              · rcases hlo_ac with heq | hlt
                · rw [← heq]
                  exact hlot
                · exact lt_trans hlt hlot
              · exact lt_trans htm (hJ₀m.right)
              · intro hex
                apply hNB₀
                obtain ⟨pc, qc, wpc, wqc, hIp, hIq, hJp, hJq,
                  hTPC, hPCm, hTQC, hQCm, hGp, hGq, hne⟩ := hex
                refine ⟨pc, qc, wpc, wqc, hIp, hIq, ?_, ?_, hGp, hGq, hne⟩
                · exact ⟨lt_trans htu₀ hTPC, lt_trans hPCm hmv₀⟩
                · exact ⟨lt_trans htu₀ hTQC, lt_trans hQCm hmv₀⟩
            · exact ⟨hlot, htm⟩
          have hlb_lo : IsLowerBound1 SL' lo := by
            intro x hx
            obtain ⟨-, hJx⟩ := hx
            exact Or.inl hJx.left
          have hSL'bd : BoundedBelow1 SL' := ⟨lo, hlb_lo⟩
          obtain ⟨sL, hsInf⟩ := infCompletenessAux SL'
            ((M.ominimal _).mp hSL'mem) hSL'ne hSL'bd
          have hExceedL : ∀ a : R, LT.lt sL a → ∃ t₁, SL (fun _ => t₁) ∧ LT.lt t₁ a := by
            intro a has
            by_contra hcon
            push Not at hcon
            have hlb : IsLowerBound1 SL' a := by
              intro x hx
              obtain ⟨hSLx, -⟩ := hx
              have e : x = fun _ => Power.coord1 x := hPtLam x
              rw [e] at hSLx
              rcases lt_trichotomy a (Power.coord1 x) with h | h | h
              · have hlt := h
                exact Or.inl hlt
              · have heq := h
                exact Or.inr heq.symm
              · have hlt := h
                exact False.elim (not_le_of_gt hlt (hcon _ hSLx))
            rcases hsInf.2 a hlb with h | h
            · exact lt_irrefl _ (lt_trans has h)
            · rw [h] at has
              exact lt_irrefl _ has
          rcases hsInf.2 lo hlb_lo with hlt | heq
          · exfalso
            have hslm : LT.lt sL m := by
              have hwit : ∃ t, SL' t := hSL'ne
              rcases hsInf.1 (hSL'ne.choose) (hSL'ne.choose_spec) with h | h
              · exact lt_trans h ((hSL'ne.choose_spec).2).right
              · rw [← h]
                exact ((hSL'ne.choose_spec).2).right
            have hJsL : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ => sL) :=
              ⟨hlt, lt_trans hslm hm_hi⟩
            have hIsL : I' (fun _ => sL) := hIcon _ hJsL
            obtain ⟨hJ₀sL, hIsLI⟩ := hIsL
            have hBsL : C (fun _ => sL) ∨ U (fun _ => sL) ∨ Dc (fun _ => sL) := by
              by_contra hcon
              have hBad : Bad (fun _ => sL) := by
                rw [hBaddef]
                refine ⟨hIcon _ hJsL, ?_⟩
                intro hc
                rcases hc with hc | hc | hc
                · exact hcon (Or.inl hc)
                · exact hcon (Or.inr (Or.inl hc))
                · exact hcon (Or.inr (Or.inr hc))
              exact (hNB _ hJsL) hBad
            rcases hBsL with hCs | hUs | hDs
            -- C window at sL: const extends left past sL.
            obtain ⟨-, -, cs, ds, hcs, hsd, hNBs⟩ := hCs
            have hcs' : LT.lt cs sL := hcs
            have hsd' : LT.lt sL ds := hsd
            obtain ⟨t', hct', hlot', ht'sL⟩ := hBetween3 cs lo sL hcs' hlt
            have hT' : SL (fun _ => t') := by
              refine ⟨⟨?_, ?_⟩, lt_trans ht'sL hslm, ?_⟩
              · rcases hlo_ac with heq2 | hlt2
                · rw [← heq2]
                  exact hlot'
                · exact lt_trans hlt2 hlot'
              · exact lt_trans ht'sL (lt_trans hslm (hJ₀m.right))
              · -- Const on (t', m].
                have hCtL : ∀ a b : R, ∀ (ha : I (fun _ => a)) (hb : I (fun _ => b)),
                    LT.lt t' a → LT.lt a m → LT.lt t' b → LT.lt b m → LT.lt a b →
                    (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨fun _ => b, hb⟩).1 := by
                  intro a b ha hb hta ham htb hbm hab
                  rcases lt_trichotomy b sL with h | h | h
                  · have hlt_bs := h
                    exact hEqWin cs ds hNBs a b ha hb
                      (lt_trans hct' hta) (lt_trans (lt_trans hab hlt_bs) hsd')
                      (lt_trans hct' htb) (lt_trans hlt_bs hsd') hab
                  · have heq_bs := h
                    have has : LT.lt a sL := by
                      rw [← heq_bs]
                      exact hab
                    have ept : (⟨fun _ => b, hb⟩ : {x : Power R 1 // I x}) =
                        ⟨fun _ => sL, hIsLI⟩ :=
                      Subtype.ext (by funext k; exact heq_bs)
                    rw [ept]
                    exact hEqWin cs ds hNBs a sL ha hIsLI
                      (lt_trans hct' hta) (lt_trans has hsd')
                      hcs' hsd' has
                  · have hlt_sb := h
                    rcases lt_trichotomy a sL with h2 | h2 | h2
                    · have hlt_as := h2
                      have e1 := hEqWin cs ds hNBs a sL ha hIsLI
                        (lt_trans hct' hta) (lt_trans hlt_as hsd')
                        hcs' hsd' hlt_as
                      obtain ⟨w, hsw, hwb, hwds⟩ := hBetween2 sL b ds hlt_sb hsd'
                      have hJw : openInterval (Endpoint.finite lo)
                          (Endpoint.finite hi) (fun _ => w) :=
                        ⟨lt_trans hlt hsw, lt_trans hwb (lt_trans hbm hm_hi)⟩
                      have hwI : I (fun _ => w) := (hIcon _ hJw).2
                      have e2a := hEqWin cs ds hNBs sL w hIsLI hwI
                        hcs' hsd' (lt_trans hcs' hsw) hwds hsw
                      obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceedL w hsw
                      have e2b := hEqSL t₁ ht₁S w b hwI hb
                        hwt₁ (lt_trans hwb hbm) (lt_trans hwt₁ hwb) hbm hwb
                      exact Eq.trans e1 (Eq.trans e2a e2b)
                    · have heq_as := h2
                      have ept : (⟨fun _ => a, ha⟩ : {x : Power R 1 // I x}) =
                          ⟨fun _ => sL, hIsLI⟩ :=
                        Subtype.ext (by funext k; exact heq_as)
                      rw [ept]
                      obtain ⟨w, hsw, hwb, hwds⟩ := hBetween2 sL b ds hlt_sb hsd'
                      have hJw : openInterval (Endpoint.finite lo)
                          (Endpoint.finite hi) (fun _ => w) :=
                        ⟨lt_trans hlt hsw, lt_trans hwb (lt_trans hbm hm_hi)⟩
                      have hwI : I (fun _ => w) := (hIcon _ hJw).2
                      have e1 := hEqWin cs ds hNBs sL w hIsLI hwI
                        hcs' hsd' (lt_trans hcs' hsw) hwds hsw
                      obtain ⟨t₁, ht₁S, hwt₁⟩ := hExceedL w hsw
                      have e2 := hEqSL t₁ ht₁S w b hwI hb
                        hwt₁ (lt_trans hwb hbm) (lt_trans hwt₁ hwb) hbm hwb
                      exact Eq.trans e1 e2
                    · have hlt_sa := h2
                      obtain ⟨t₁, ht₁S, htt₁⟩ := hExceedL a hlt_sa
                      exact hEqSL t₁ ht₁S a b ha hb htt₁ ham
                        (lt_trans htt₁ hab) hbm hab
                intro hex
                obtain ⟨a, b, wpc, wqc, hIp, hIq, hJp, hJq,
                  hta, ham, htb, hbm, hGp, hGq, hne⟩ := hex
                rcases lt_trichotomy a b with hab | hab | hab
                · have hlt_ab := hab
                  have heqAB := hCtL a b hIp hIq hta ham htb hbm hlt_ab
                  have hwpc := wpcEqVal f a wpc hIp hGp
                  have hwqc := wpcEqVal f b wqc hIq hGq
                  have hr : wpc = wqc := hwpc.trans
                    ((congrArg (· 0) heqAB).trans hwqc.symm)
                  exact hne (congrArg (fun w : R => (fun _ : Fin 1 => w)) hr)
                · have heq_ab := hab
                  have ept : (⟨fun _ => b, hIq⟩ : {x : Power R 1 // I x}) =
                      ⟨fun _ => a, hIp⟩ := Subtype.ext
                    (congrArg (fun c : R => (fun _ : Fin 1 => c)) heq_ab.symm)
                  have hwpc := wpcEqVal f a wpc hIp hGp
                  have hwqc := wpcEqVal f b wqc hIq hGq
                  rw [ept] at hwqc
                  rw [hwpc, hwqc] at hne
                  exact False.elim (hne rfl)
                · have hlt_ba := hab
                  have heqAB := hCtL b a hIq hIp htb hbm hta ham hlt_ba
                  have hwpc := wpcEqVal f a wpc hIp hGp
                  have hwqc := wpcEqVal f b wqc hIq hGq
                  have hr : wpc = wqc := hwpc.trans
                    ((congrArg (· 0) heqAB.symm).trans hwqc.symm)
                  exact hne (congrArg (fun w : R => (fun _ : Fin 1 => w)) hr)
            have ht'S : SL' (fun _ => t') := ⟨hT', ⟨hlot', lt_trans ht'sL hslm⟩⟩
            rcases hsInf.1 (fun _ => t') ht'S with h | h
            · exact lt_irrefl _ (lt_trans h ht'sL)
            · rw [← h] at ht'sL
              exact lt_irrefl _ ht'sL
            · -- U window at sL meets sL's C window: contradiction.
              obtain ⟨-, -, csU, dsU, hcsU, hsdU, hNBu⟩ := hUs
              obtain ⟨-, -, csC, dsC, hcsC, hsdC, hNBC⟩ := hCcon _ hJsL
              have hcsU' : LT.lt csU sL := hcsU
              have hsdU' : LT.lt sL dsU := hsdU
              have hcsC' : LT.lt csC sL := hcsC
              have hsdC' : LT.lt sL dsC := hsdC
              obtain ⟨z₁, hlo₁, hcC₁, hz₁s⟩ := hBetween3 lo csC sL hlt hcsC'
              obtain ⟨z₂, hz₁₂, hcU₂, hz₂s⟩ := hBetween3 z₁ csU sL hz₁s hcsU'
              obtain ⟨u₁, hzu₁, hu₁s⟩ := exists_between hz₂s
              obtain ⟨u₂, h1u₂, hu₂s⟩ := exists_between hu₁s
              have hu₁lo : LT.lt lo u₁ := lt_trans hlo₁ (lt_trans hz₁₂ hzu₁)
              have hu₁hi : LT.lt u₁ hi := lt_trans hu₁s (lt_trans hslm hm_hi)
              have hu₂lo : LT.lt lo u₂ := lt_trans hlo₁ (lt_trans hz₁₂ (lt_trans hzu₁ h1u₂))
              have hu₂hi : LT.lt u₂ hi := lt_trans hu₂s (lt_trans hslm hm_hi)
              have hJ₁ : openInterval (Endpoint.finite lo)
                  (Endpoint.finite hi) (fun _ => u₁) :=
                ⟨hu₁lo, hu₁hi⟩
              have hJ₂ : openInterval (Endpoint.finite lo)
                  (Endpoint.finite hi) (fun _ => u₂) :=
                ⟨hu₂lo, hu₂hi⟩
              have hI₁ : I (fun _ => u₁) := (hIcon _ hJ₁).2
              have hI₂ : I (fun _ => u₂) := (hIcon _ hJ₂).2
              have hu₁cC : LT.lt csC u₁ := lt_trans hcC₁ (lt_trans hz₁₂ hzu₁)
              have hu₂cC : LT.lt csC u₂ := lt_trans hcC₁ (lt_trans hz₁₂ (lt_trans hzu₁ h1u₂))
              have hu₁dC : LT.lt u₁ dsC := lt_trans hu₁s hsdC'
              have hu₂dC : LT.lt u₂ dsC := lt_trans hu₂s hsdC'
              have hu₁cU : LT.lt csU u₁ := lt_trans hcU₂ hzu₁
              have hu₂cU : LT.lt csU u₂ := lt_trans hcU₂ (lt_trans hzu₁ h1u₂)
              have hu₁dU : LT.lt u₁ dsU := lt_trans hu₁s hsdU'
              have hu₂dU : LT.lt u₂ dsU := lt_trans hu₂s hsdU'
              have heq12 := hEqWin csC dsC hNBC u₁ u₂ hI₁ hI₂
                hu₁cC hu₁dC hu₂cC hu₂dC h1u₂
              have hw12 : (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0 =
                  (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0 :=
                congrArg (· 0) heq12
              apply hNBu
              refine ⟨u₁, u₂, (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0,
                (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0,
                hI₁, hI₂, ⟨hu₁cU, hu₁dU⟩, ⟨hu₂cU, hu₂dU⟩,
                h1u₂, graphAppendConst f _ hI₁, graphAppendConst f _ hI₂,
                Or.inr ?_⟩
              show (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0) =
                (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0)
              exact congrArg (fun w => (fun _ : Fin 1 => w)) hw12
            · -- Dc window at sL meets sL's C window: contradiction.
              obtain ⟨-, -, csD, dsD, hcsD, hsdD, hNBd⟩ := hDs
              obtain ⟨-, -, csC, dsC, hcsC, hsdC, hNBC⟩ := hCcon _ hJsL
              have hcsD' : LT.lt csD sL := hcsD
              have hsdD' : LT.lt sL dsD := hsdD
              have hcsC' : LT.lt csC sL := hcsC
              have hsdC' : LT.lt sL dsC := hsdC
              obtain ⟨z₁, hlo₁, hcC₁, hz₁s⟩ := hBetween3 lo csC sL hlt hcsC'
              obtain ⟨z₂, hz₁₂, hcD₂, hz₂s⟩ := hBetween3 z₁ csD sL hz₁s hcsD'
              obtain ⟨u₁, hzu₁, hu₁s⟩ := exists_between hz₂s
              obtain ⟨u₂, h1u₂, hu₂s⟩ := exists_between hu₁s
              have hu₁lo : LT.lt lo u₁ := lt_trans hlo₁ (lt_trans hz₁₂ hzu₁)
              have hu₁hi : LT.lt u₁ hi := lt_trans hu₁s (lt_trans hslm hm_hi)
              have hu₂lo : LT.lt lo u₂ := lt_trans hlo₁ (lt_trans hz₁₂ (lt_trans hzu₁ h1u₂))
              have hu₂hi : LT.lt u₂ hi := lt_trans hu₂s (lt_trans hslm hm_hi)
              have hJ₁ : openInterval (Endpoint.finite lo)
                  (Endpoint.finite hi) (fun _ => u₁) :=
                ⟨hu₁lo, hu₁hi⟩
              have hJ₂ : openInterval (Endpoint.finite lo)
                  (Endpoint.finite hi) (fun _ => u₂) :=
                ⟨hu₂lo, hu₂hi⟩
              have hI₁ : I (fun _ => u₁) := (hIcon _ hJ₁).2
              have hI₂ : I (fun _ => u₂) := (hIcon _ hJ₂).2
              have hu₁cC : LT.lt csC u₁ := lt_trans hcC₁ (lt_trans hz₁₂ hzu₁)
              have hu₂cC : LT.lt csC u₂ := lt_trans hcC₁ (lt_trans hz₁₂ (lt_trans hzu₁ h1u₂))
              have hu₁dC : LT.lt u₁ dsC := lt_trans hu₁s hsdC'
              have hu₂dC : LT.lt u₂ dsC := lt_trans hu₂s hsdC'
              have hu₁cD : LT.lt csD u₁ := lt_trans hcD₂ hzu₁
              have hu₂cD : LT.lt csD u₂ := lt_trans hcD₂ (lt_trans hzu₁ h1u₂)
              have hu₁dD : LT.lt u₁ dsD := lt_trans hu₁s hsdD'
              have hu₂dD : LT.lt u₂ dsD := lt_trans hu₂s hsdD'
              have heq12 := hEqWin csC dsC hNBC u₁ u₂ hI₁ hI₂
                hu₁cC hu₁dC hu₂cC hu₂dC h1u₂
              have hw12 : (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0 =
                  (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0 :=
                congrArg (· 0) heq12
              apply hNBd
              refine ⟨u₁, u₂, (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0,
                (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0,
                hI₁, hI₂, ⟨hu₁cD, hu₁dD⟩, ⟨hu₂cD, hu₂dD⟩,
                h1u₂, graphAppendConst f _ hI₁, graphAppendConst f _ hI₂,
                Or.inr ?_⟩
              show (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₁, hI₁⟩).1 0) =
                (fun _ : Fin 1 => (f.toFun ⟨fun _ => u₂, hI₂⟩).1 0)
              exact congrArg (fun w => (fun _ : Fin 1 => w)) hw12
          · subst heq
            have hAnchorL : ∀ a : R, ∀ (ha : I (fun _ => a)), LT.lt lo a → LT.lt a m →
                (f.toFun ⟨fun _ => a, ha⟩).1 = (f.toFun ⟨xm, hImm⟩).1 := by
              intro a ha hlo_a ham
              obtain ⟨b₀, hab₀, hub₀, hb₀m⟩ := hBetween3 a u₀ m ham hmu₀
              have hb₀v : LT.lt b₀ v₀ := lt_trans hb₀m hmv₀
              have hb₀I : I (fun _ => b₀) := by
                have hJ : openInterval (Endpoint.finite lo)
                    (Endpoint.finite hi) (fun _ => b₀) :=
                  ⟨lt_trans hlo_a hab₀, lt_trans hb₀m hm_hi⟩
                exact (hIcon _ hJ).2
              obtain ⟨t₁, ht₁S, htt₁⟩ := hExceedL a hlo_a
              have e1 := hEqSL t₁ ht₁S a b₀ ha hb₀I htt₁ ham
                (lt_trans htt₁ hab₀) hb₀m hab₀
              have e2 := hEqWin u₀ v₀ hNB₀ b₀ m hb₀I hImm hub₀ hb₀v
                hmu₀ hmv₀ hb₀m
              exact Eq.trans e1 e2
            have hVlam : ∀ c : R, ∀ (hcI : I (fun _ => c)),
                LT.lt lo c → LT.lt c hi →
                (f.toFun ⟨fun _ => c, hcI⟩).1 = (f.toFun ⟨xm, hImm⟩).1 := by
              intro c hcI hlo_c hchi
              rcases lt_trichotomy c m with h | h | h
              · have hlt := h
                exact hAnchorL _ hcI hlo_c hlt
              · have heq2 := h
                have ept : (⟨fun _ => c, hcI⟩ : {x : Power R 1 // I x}) = ⟨xm, hImm⟩ :=
                  Subtype.ext (congrArg (fun r : R => (fun _ : Fin 1 => r)) heq2)
                rw [ept]
              · have hlt := h
                exact hAnchorR _ hcI hlt hchi
            have hV : ∀ z : Power R 1, ∀ (hzI : I z),
                openInterval (Endpoint.finite lo) (Endpoint.finite hi) z →
                (f.toFun ⟨z, hzI⟩).1 = (f.toFun ⟨xm, hImm⟩).1 := by
              intro z hzI hJz
              have hzI2 : I (fun _ => Power.coord1 z) := by
                rw [← hPtLam z]
                exact hzI
              have hJz2 : openInterval (Endpoint.finite lo) (Endpoint.finite hi)
                  (fun _ => Power.coord1 z) := by
                rw [hPtLam z] at hJz
                exact hJz
              have ept : (⟨z, hzI⟩ : {x : Power R 1 // I x}) =
                  ⟨fun _ => Power.coord1 z, hzI2⟩ := Subtype.ext (hPtLam z)
              rw [ept]
              exact hVlam _ hzI2 hJz2.left hJz2.right
            refine Or.inl ⟨?_, ?_⟩
            · intro x hxI hJx y hyI hJy
              exact Subtype.ext (Eq.trans (hV x hxI hJx) (Eq.symm (hV y hyI hJy)))
            · exact Monotonicity_Theorem.const_cont_of_const M f lo hi
                (fun x hJx => (hIcon x hJx).2)
                (fun x hxI hJx y hyI hJy =>
                  Eq.trans (hV x hxI hJx) (Eq.symm (hV y hyI hJy)))
