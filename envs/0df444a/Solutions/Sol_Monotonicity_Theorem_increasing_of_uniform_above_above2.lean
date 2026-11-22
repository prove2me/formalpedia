-- Prove2me | solution 1 for Monotonicity_Theorem.increasing_of_uniform_above_above2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T00:46:01.495769+00:00
-- url     : https://prove2.me/submissions/3b64bb5e-b3f6-4ae6-ab61-5e7e7290bea7

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval2
import Mathlib.Data.Finset.Max

open Classical
open Monotonicity_Theorem

theorem Monotonicity_Theorem.incompatible_decreasing_above_above {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Endpoint R} (hsubJ : ∀ x, openInterval a b x → I x)
    (hU : ∀ x (hxI : I x), openInterval a b x ->
        ∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
        Lt1 c1 x ∧ Lt1 x c2 ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 c1 y → Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 x y → Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1))
    {u v : R} (huv : LT.lt u v)
    (hsub : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval a b x)
    (hdec : ∀ x (hxI : I x) y (hyI : I y),
      openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval (Endpoint.finite u) (Endpoint.finite v) y ->
      Lt1 x y → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) :
    False := by
  obtain ⟨r1, hxr1, hr1v⟩ := exists_between huv
  have hxJ : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => r1) :=
    ⟨hxr1, hr1v⟩
  have hxI : I (fun _ => r1) := hsubJ _ (hsub _ hxJ)
  obtain ⟨c1, c2, hc1J, hc2J, hc1x, hxc2, hleft, hright⟩ :=
    hU (fun _ => r1) hxI (hsub _ hxJ)
  have hxc2c : LT.lt r1 (Power.coord1 c2) := hxc2
  have hpick : ∃ rr : R, LT.lt r1 rr ∧ LT.lt rr (Power.coord1 c2) ∧ LT.lt rr v := by
    rcases lt_trichotomy (Power.coord1 c2) v with h | h | h
    · have hlt1 := h
      obtain ⟨s, hs1, hs2⟩ := exists_between hxc2c
      refine ⟨s, hs1, hs2, ?_⟩
      exact lt_trans hs2 hlt1
    · have heq := h
      obtain ⟨s, hs1, hs2⟩ := exists_between hxc2c
      refine ⟨s, hs1, hs2, ?_⟩
      rw [← heq]
      exact hs2
    · have hlt1 := h
      obtain ⟨s, hs1, hs2⟩ := exists_between hr1v
      exact ⟨s, hs1, lt_trans hs2 hlt1, hs2⟩
  obtain ⟨rr, hrr1, hrr2, hrr3⟩ := hpick
  have hzJ : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => rr) :=
    ⟨lt_trans hxr1 hrr1, hrr3⟩
  have hzI : I (fun _ => rr) := hsubJ _ (hsub _ hzJ)
  have hxz : Lt1 (fun _ => r1) (fun _ => rr) := hrr1
  have hdecXZ : Lt1 (f.toFun (Subtype.mk (fun _ => rr) hzI)).1
      (f.toFun (Subtype.mk (fun _ => r1) hxI)).1 :=
    hdec _ hxI _ hzI hxJ hzJ hxz
  have hwin : Lt1 (f.toFun (Subtype.mk (fun _ => r1) hxI)).1
      (f.toFun (Subtype.mk (fun _ => rr) hzI)).1 := by
    have hzJab : openInterval a b (fun _ => rr) := hsub _ hzJ
    have hxzab : Lt1 (fun _ => r1) (fun _ => rr) := hrr1
    have hzc2 : Lt1 (fun _ => rr) c2 := hrr2
    exact hright _ hzI hzJab hxzab hzc2
  exact lt_irrefl _ (lt_trans hwin hdecXZ)

theorem Monotonicity_Theorem.incompatible_increasing_above_above {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Endpoint R} (hsubJ : ∀ x, openInterval a b x → I x)
    (hU : ∀ x (hxI : I x), openInterval a b x ->
        ∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
        Lt1 c1 x ∧ Lt1 x c2 ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 c1 y → Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 x y → Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1))
    {u v : R} (huv : LT.lt u v)
    (hsub : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval a b x)
    (hinc : ∀ x (hxI : I x) y (hyI : I y),
      openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval (Endpoint.finite u) (Endpoint.finite v) y ->
      Lt1 x y → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) :
    False := by
  obtain ⟨r1, hxr1, hr1v⟩ := exists_between huv
  have hx0J : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => r1) :=
    ⟨hxr1, hr1v⟩
  obtain ⟨r2, hxr2, hr2v⟩ := exists_between hr1v
  have hyJ : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => r2) :=
    ⟨lt_trans hxr1 hxr2, hr2v⟩
  have hx0I : I (fun _ => r1) := hsubJ _ (hsub _ hx0J)
  have hyI : I (fun _ => r2) := hsubJ _ (hsub _ hyJ)
  have hxy : Lt1 (fun _ => r1) (fun _ => r2) := hxr2
  obtain ⟨c1, c2, hc1J, hc2J, hc1y, hyc2, hleft, hright⟩ :=
    hU (fun _ => r2) hyI (hsub _ hyJ)
  have hc1c : LT.lt (Power.coord1 c1) r2 := hc1y
  have hpick : ∃ rr : R, LT.lt (Power.coord1 (fun _ => r1)) rr ∧
      LT.lt (Power.coord1 c1) rr ∧ LT.lt rr r2 := by
    rcases lt_trichotomy (Power.coord1 (fun _ => r1)) (Power.coord1 c1) with h | h | h
    · have hlt1 := h
      obtain ⟨s, hs1, hs2⟩ := exists_between hc1c
      exact ⟨s, lt_trans hlt1 hs1, hs1, hs2⟩
    · have heq := h
      obtain ⟨s, hs1, hs2⟩ := exists_between hc1c
      refine ⟨s, ?_, hs1, hs2⟩
      rw [heq]
      exact hs1
    · have hlt1 := h
      obtain ⟨s, hs1, hs2⟩ := exists_between hxr2
      exact ⟨s, hs1, lt_trans hlt1 hs1, hs2⟩
  obtain ⟨rr, hrr1, hrr2, hrr3⟩ := hpick
  have hzJ : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => rr) :=
    ⟨lt_trans hxr1 hrr1, lt_trans hrr3 hr2v⟩
  have hzI : I (fun _ => rr) := hsubJ _ (hsub _ hzJ)
  have hzy : Lt1 (fun _ => rr) (fun _ => r2) := hrr3
  have hincZY : Lt1 (f.toFun (Subtype.mk (fun _ => rr) hzI)).1
      (f.toFun (Subtype.mk (fun _ => r2) hyI)).1 :=
    hinc _ hzI _ hyI hzJ hyJ hzy
  have hwin : Lt1 (f.toFun (Subtype.mk (fun _ => r2) hyI)).1
      (f.toFun (Subtype.mk (fun _ => rr) hzI)).1 := by
    have hzJab : openInterval a b (fun _ => rr) := hsub _ hzJ
    have hc1z : Lt1 c1 (fun _ => rr) := hrr2
    have hzyab : Lt1 (fun _ => rr) (fun _ => r2) := hrr3
    exact hleft _ hzI hzJab hc1z hzyab
  exact lt_irrefl _ (lt_trans hincZY hwin)



namespace Monotonicity_Theorem

-- Inlined order-bound infrastructure (verbatim copy of the Bounds definition
-- file, so this public proof needs no private imports).
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

namespace Monotonicity_Theorem

-- Index maps into arity 1 + (1 + 1).
-- Positions (flattened): s = 0, z = 1, w = 2.
-- The failure matrix records a counter z with value w at or below v0.
def baS : Fin 1 → Fin (1 + (1 + 1)) :=
  fun _ => ⟨0, by decide⟩

def baZ : Fin 1 → Fin (1 + (1 + 1)) :=
  fun _ => ⟨1, by decide⟩

def baW : Fin 1 → Fin (1 + (1 + 1)) :=
  fun _ => ⟨2, by decide⟩

def baLT : Fin 2 → Fin (1 + (1 + 1)) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

def baG : Fin (1 + 1) → Fin (1 + (1 + 1)) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩

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

-- Inlined supremum tower (verbatim copies of the private completeness proofs,
-- renamed, so this public proof needs no private imports).
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

-- Below-sup points exist (from least-upper-bound property).
theorem notUBofLeast {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (m : R)
    (hLeast : ∀ bnd, IsUpperBound1 A bnd → (LT.lt m bnd ∨ m = bnd))
    (t : R) (htm : LT.lt t m) : ∃ s, A s ∧ LT.lt t (Power.coord1 s) := by
  by_contra hne
  have htUB : IsUpperBound1 A t := by
    intro s hs
    rcases lt_trichotomy t (Power.coord1 s) with h | h | h
    · exact False.elim (hne ⟨s, hs, h⟩)
    · have heq := h
      exact Or.inr heq.symm
    · have hlt2 := h
      exact Or.inl hlt2
  rcases hLeast t htUB with h | h
  · exact lt_irrefl _ (lt_trans htm h)
  · rw [h] at htm
    exact lt_irrefl _ htm


-- A nonempty open interval contains a finite-endpoint subwindow.
theorem finiteSubwindow {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
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

namespace Monotonicity_Theorem

-- Index maps into arity 1 + (1 + (1 + 1)) for left-minima.
-- Positions (flattened): x = 0, y = 1, w = 2, v = 3.
-- The failure matrix records y left of x whose value does not exceed x's.
def lMX : Fin 1 → Fin (1 + (1 + (1 + 1))) :=
  fun _ => ⟨0, by decide⟩

def lMY : Fin 1 → Fin (1 + (1 + (1 + 1))) :=
  fun _ => ⟨1, by decide⟩

def lMLT : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

def lMGW : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩

def lMGX : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩

def lMBAD : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨3, by decide⟩

def preW : Fin 1 → Fin (1 + 1) := fun _ => ⟨1, by decide⟩

end Monotonicity_Theorem

open Monotonicity_Theorem

-- Left-global minima on a window form a definable set.
theorem leftMinDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R) :
    M.S 1 (fun x : Power R 1 => openInterval a b x ∧
      ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 y x ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) ->
        Lt1 v w) := by
  have hJmem : M.S 1 (openInterval a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hF : M.S (1 + (1 + (1 + 1)))
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (lMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem lMX hJmem)
      (M.inter_mem (M.reindex_mem lMY f.domain_mem)
        (M.inter_mem (M.reindex_mem lMY hJmem)
          (M.inter_mem (M.reindex_mem lMLT M.lt_mem)
            (M.inter_mem (M.reindex_mem lMGW f.graph_mem)
              (M.inter_mem (M.reindex_mem lMGX f.graph_mem)
                (M.union_mem (M.reindex_mem lMBAD M.lt_mem)
                  (M.diagonal_mem (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
                    (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) (by decide))))))))
  have hProj : M.S 1 (fun x : Power R 1 => ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (lMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)) :=
    M.existsLast_mem hF
  have hC : M.S 1 (fun x : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (lMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)) :=
    M.compl_mem hProj
  have hJX : M.S 1 ((openInterval a b) ∩
      (fun x : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (lMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t))) :=
    M.inter_mem hJmem hC
  have heq : ((openInterval a b) ∩
      (fun x : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (lMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)))
      = (fun x : Power R 1 => openInterval a b x ∧
        ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 y x ->
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w) ->
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x v) ->
          Lt1 v w) := by
    funext x
    apply propext
    constructor
    · intro h
      obtain ⟨hJx, hn⟩ := h
      refine ⟨hJx, ?_⟩
      intro y w v hy hyJ hxy hGyw hGxv
      have eY : (fun i : Fin 1 => (Power.append x
              (Power.append y (Power.append w v))) (lMY i)) = y := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      have gXY : LT.lt ((fun j : Fin 2 => (Power.append x
              (Power.append y (Power.append w v))) (lMLT j)) 0)
          ((fun j : Fin 2 => (Power.append x
              (Power.append y (Power.append w v))) (lMLT j)) 1) := hxy
      have eGW : (fun j : Fin (1 + 1) => (Power.append x
              (Power.append y (Power.append w v))) (lMGW j))
          = Power.append y w := by
        funext j
        by_cases hj : j.val = 0
        · have e : lMGW j
              = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGW, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x
                (Power.append y (Power.append w v))) (lMGW j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj0]
        · have e : lMGW j
              = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGW, hj]
          have jv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append x
                (Power.append y (Power.append w v))) (lMGW j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = w ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => (Power.append x
              (Power.append y (Power.append w v))) (lMGX j))
          = Power.append x v := by
        funext j
        by_cases hj : j.val = 0
        · have e : lMGX j
              = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGX, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x
                (Power.append y (Power.append w v))) (lMGX j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x v)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x v (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x v) j := by rw [hj0]
        · have e : lMGX j
              = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGX, hj]
          have jv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append x
                (Power.append y (Power.append w v))) (lMGX j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = v ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x v)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right x v (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x v) j := by rw [hj1]
      have hIY : I (fun i : Fin 1 => (Power.append x
          (Power.append y (Power.append w v))) (lMY i)) := by
        rw [eY]
        exact hy
      have hJY : openInterval a b (fun i : Fin 1 => (Power.append x
          (Power.append y (Power.append w v))) (lMY i)) := by
        rw [eY]
        exact hyJ
      have hGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => (Power.append x
            (Power.append y (Power.append w v))) (lMGW j)) := by
        rw [eGW]
        exact hGyw
      have hGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => (Power.append x
            (Power.append y (Power.append w v))) (lMGX j)) := by
        rw [eGX]
        exact hGxv
      cases lt_trichotomy (Power.coord1 v) (Power.coord1 w) with
      | inl hTri =>
        exact hTri
      | inr h =>
        cases h with
        | inl h =>
          have gEq : (Power.append x (Power.append y (Power.append w v)))
                (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
              = (Power.append x (Power.append y (Power.append w v)))
                (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := h.symm
          exact False.elim (hn ⟨Power.append y (Power.append w v),
            hJx, hIY, hJY, gXY, hGW, hGX, Or.inr gEq⟩)
        | inr h =>
          have gLt : LT.lt ((fun j : Fin 2 => (Power.append x
                  (Power.append y (Power.append w v))) (lMBAD j)) 0)
              ((fun j : Fin 2 => (Power.append x
                  (Power.append y (Power.append w v))) (lMBAD j)) 1) := h
          exact False.elim (hn ⟨Power.append y (Power.append w v),
            hJx, hIY, hJY, gXY, hGW, hGX, Or.inl gLt⟩)
    · intro ⟨hJx, hall⟩
      refine ⟨hJx, ?_⟩
      intro hF1
      obtain ⟨t, hJxF, hIyF, hJyF, hLT, hGW, hGX, hBad⟩ := hF1
      set y : Power R 1 := fun _ => (Power.append x t)
        (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) with hydef
      set w : Power R 1 := fun _ => (Power.append x t)
        (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) with hwdef
      set v : Power R 1 := fun _ => (Power.append x t)
        (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) with hvdef
      have eY' : (fun i : Fin 1 => (Power.append x t) (lMY i)) = y := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      have eGWt : (fun j : Fin (1 + 1) => (Power.append x t) (lMGW j))
          = Power.append y w := by
        funext j
        by_cases hj : j.val = 0
        · have e : lMGW j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGW, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x t) (lMGW j)
              = (Power.append x t) (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj0]
        · have e : lMGW j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGW, hj]
          have hjv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
          calc (Power.append x t) (lMGW j)
              = (Power.append x t) (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = w ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj1]
      have eGXt : (fun j : Fin (1 + 1) => (Power.append x t) (lMGX j))
          = Power.append x v := by
        funext j
        by_cases hj : j.val = 0
        · have e : lMGX j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGX, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x t) (lMGX j)
              = (Power.append x t) (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x v)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x v (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x v) j := by rw [hj0]
        · have e : lMGX j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [lMGX, hj]
          have hjv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
          calc (Power.append x t) (lMGX j)
              = (Power.append x t) (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = v ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x v)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right x v (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x v) j := by rw [hj1]
      have hy : I y := by
        rw [← eY']
        exact hIyF
      have hyJ : openInterval a b y := by
        rw [← eY']
        exact hJyF
      have hxy : Lt1 y x := hLT
      have hGyw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) := by
        rw [← eGWt]
        exact hGW
      have hGxv : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) := by
        rw [← eGXt]
        exact hGX
      have hval : Lt1 v w := hall y w v hy hyJ hxy hGyw hGxv
      rcases hBad with hLT2 | hEQ
      · have hval' : LT.lt (Power.coord1 v) (Power.coord1 w) := hval
        have hlt2' : LT.lt (Power.coord1 w) (Power.coord1 v) := hLT2
        exact lt_irrefl _ (lt_trans hval' hlt2')
      · have heq' : Power.coord1 w = Power.coord1 v := hEQ
        have hval' : LT.lt (Power.coord1 v) (Power.coord1 w) := hval
        rw [heq'] at hval'
        exact lt_irrefl _ hval'
  rw [← heq]
  exact hJX

-- Values below a fixed bound attained on a window: preimage is definable.
theorem belowPreimageDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R)
    (x₀ : Power R 1) (hx₀I : I x₀) :
    M.S 1 (fun y : Power R 1 => openInterval a b y ∧
      Lt1 y x₀ ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1)) := by
  have hJmem : M.S 1 (openInterval a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hXLT : M.S 1 (openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hW : M.S 1 (openInterval Endpoint.negInf
      (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hG2 : M.S (1 + 1)
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i))) :=
    M.inter_mem f.graph_mem (M.reindex_mem preW hW)
  have hPRE : M.S 1 (fun y : Power R 1 => ∃ w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w)) :=
    M.existsLast_mem hG2
  have hS : M.S 1 (((openInterval a b) ∩
      (openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀)))) ∩
      (fun y : Power R 1 => ∃ w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w))) :=
    M.inter_mem (M.inter_mem hJmem hXLT) hPRE
  have heqS : (((openInterval a b) ∩
      (openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀)))) ∩
      (fun y : Power R 1 => ∃ w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w)))
      = (fun y : Power R 1 => openInterval a b y ∧
        Lt1 y x₀ ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1)) := by
    funext y
    apply propext
    constructor
    · intro h
      obtain ⟨hJX, hRest⟩ := h
      obtain ⟨hJy, hXy⟩ := hJX
      obtain ⟨w, hG, hWlt⟩ := hRest
      have hxy : Lt1 y x₀ := by
        obtain ⟨-, hlt1⟩ := hXy
        exact hlt1
      have hwlt : Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1 := by
        obtain ⟨-, hlt1⟩ := hWlt
        exact hlt1
      exact ⟨hJy, hxy, ⟨w, hG, hwlt⟩⟩
    · intro h
      obtain ⟨hJy, hxy, hPREw⟩ := h
      obtain ⟨w, hG, hwlt⟩ := hPREw
      have hXy : openInterval Endpoint.negInf
          (Endpoint.finite (Power.coord1 x₀)) y := ⟨trivial, hxy⟩
      have hWlt : openInterval Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1))) w :=
        ⟨trivial, hwlt⟩
      exact ⟨⟨hJy, hXy⟩, ⟨w, hG, hWlt⟩⟩
  rw [← heqS]
  exact hS

namespace Monotonicity_Theorem

-- Index maps into arity 1 + (1 + (1 + 1)) for candidates.
-- Positions (flattened): y = 0, z = 1, w1 = 2, w2 = 3.
def tCZ : Fin 1 → Fin (1 + (1 + (1 + 1))) :=
  fun _ => ⟨1, by decide⟩

def tLTyz : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

def tG1 : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩

def tG2 : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨3, by decide⟩

def tBAD : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨3, by decide⟩ else ⟨2, by decide⟩

end Monotonicity_Theorem

open Monotonicity_Theorem

-- Candidate sets (left-to-x0 minima below x0's value) are definable.
theorem candDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R)
    (x₀ : Power R 1) (hx₀I : I x₀) :
    M.S 1 (fun y : Power R 1 => openInterval a b y ∧ Lt1 y x₀ ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
      (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
        Lt1 y z → Lt1 z x₀ →
        (LT.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 w1 (f.toFun (Subtype.mk z hzI)).1)) := by
  have hJmem : M.S 1 (openInterval a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hXz : M.S 1 (openInterval Endpoint.negInf
      (Endpoint.finite (Power.coord1 x₀))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hPREfull : M.S 1 (fun y : Power R 1 => openInterval a b y ∧
      Lt1 y x₀ ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1)) :=
    belowPreimageDefinable M f a b x₀ hx₀I
  have hF : M.S (1 + (1 + (1 + 1)))
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem tCZ f.domain_mem)
      (M.inter_mem (M.reindex_mem tCZ hJmem)
        (M.inter_mem (M.reindex_mem tCZ hXz)
          (M.inter_mem (M.reindex_mem tLTyz M.lt_mem)
            (M.inter_mem
              (M.union_mem (M.reindex_mem tLTyz M.lt_mem)
                (M.diagonal_mem (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
                  (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) (by decide)))
              (M.inter_mem (M.reindex_mem tG1 f.graph_mem)
                (M.inter_mem (M.reindex_mem tG2 f.graph_mem)
                  (M.union_mem (M.reindex_mem tBAD M.lt_mem)
                    (M.diagonal_mem (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
                      (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) (by decide)))))))))
  have hProj : M.S 1 (fun y : Power R 1 => ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 1 (fun y : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)) :=
    M.compl_mem hProj
  have hPREfull : M.S 1 (fun y : Power R 1 => openInterval a b y ∧
      Lt1 y x₀ ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1)) :=
    belowPreimageDefinable M f a b x₀ hx₀I
  have hTmem : M.S 1 (setInter
      (fun y : Power R 1 => openInterval a b y ∧
        Lt1 y x₀ ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1))
      (fun y : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t))) :=
    M.inter_mem hPREfull hC
  have heqT : (setInter
      (fun y : Power R 1 => openInterval a b y ∧
        Lt1 y x₀ ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1))
      (fun y : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)))
      = (fun y : Power R 1 => openInterval a b y ∧ Lt1 y x₀ ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
        (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
          Lt1 y z → Lt1 z x₀ →
          (LT.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w1) →
          Lt1 w1 (f.toFun (Subtype.mk z hzI)).1)) := by
    funext y
    apply propext
    constructor
    · intro h
      obtain ⟨hPRE, hn⟩ := h
      obtain ⟨hJy, hXy, hPREw⟩ := hPRE
      obtain ⟨wY, hGY, hWlt⟩ := hPREw
      have hltYX : Lt1 y x₀ := hXy
      refine ⟨hJy, hltYX, ⟨wY, hGY, hWlt⟩, ?_⟩
      intro z w1 hzI hzJ hyz hzx hle hGyw1
      have eW2 : (f.toFun (Subtype.mk z hzI)).1
          = Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) := by
        rw [appendRightAux]
      have eL2 : Power.left (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) = z :=
        appendLeftAux _ _
      have eR2 : Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) =
          (f.toFun (Subtype.mk z hzI)).1 :=
        appendRightAux _ _
      have hGzw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) :=
        ⟨eL2.symm ▸ hzI, by simp only [eL2, eR2]⟩
      rcases lt_trichotomy (Power.coord1 w1)
          (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) with
        hTri | heqC | hgtC
      · have hv : Lt1 w1 ((f.toFun (Subtype.mk z hzI)).1) := hTri
        exact hv
      · have heqV := heqC
        exfalso
        apply hn
        use Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1))
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tCZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzI
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tCZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzJ
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tCZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact ⟨trivial, hzx⟩
        · exact hyz
        · cases hle with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h
        · have eT1t : (fun j : Fin (1 + 1) => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tG1 j))
              = Power.append y w1 := by
            funext j
            by_cases hj : j.val = 0
            · have e : tG1 j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG1, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG1 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append y w1)
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left y w1 (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append y w1) j := by rw [hj0]
            · have e : tG1 j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG1, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG1 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = w1 ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append y w1)
                    (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_right y w1 (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append y w1) j := by rw [hj1]
          rw [eT1t]
          exact hGyw1
        · have eT2t : (fun j : Fin (1 + 1) => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tG2 j))
              = Power.append z ((f.toFun (Subtype.mk z hzI)).1) := by
            funext j
            by_cases hj : j.val = 0
            · have e : tG2 j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG2, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG2 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left z _ (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj0]
            · have e : tG2 j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG2, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG2 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = ((f.toFun (Subtype.mk z hzI)).1) ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                    (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_right z _ (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj1]
          rw [eT2t]
          exact hGzw
        · exact Or.inr heqV
      · have hgt := hgtC
        exfalso
        apply hn
        use Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1))
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tCZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzI
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tCZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzJ
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tCZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact ⟨trivial, hzx⟩
        · exact hyz
        · cases hle with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h
        · have eT1t : (fun j : Fin (1 + 1) => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tG1 j))
              = Power.append y w1 := by
            funext j
            by_cases hj : j.val = 0
            · have e : tG1 j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG1, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG1 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append y w1)
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left y w1 (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append y w1) j := by rw [hj0]
            · have e : tG1 j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG1, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG1 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = w1 ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append y w1)
                    (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_right y w1 (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append y w1) j := by rw [hj1]
          rw [eT1t]
          exact hGyw1
        · have eT2t : (fun j : Fin (1 + 1) => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tG2 j))
              = Power.append z ((f.toFun (Subtype.mk z hzI)).1) := by
            funext j
            by_cases hj : j.val = 0
            · have e : tG2 j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG2, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG2 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left z _ (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj0]
            · have e : tG2 j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tG2, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tG2 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = ((f.toFun (Subtype.mk z hzI)).1) ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                    (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_right z _ (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj1]
          rw [eT2t]
          exact hGzw
        · exact Or.inl hgt
    · intro h
      obtain ⟨hJy, hXy, hPREw, hall⟩ := h
      refine ⟨?_, ?_⟩
      · refine ⟨hJy, hXy, hPREw⟩
      · intro hex
        obtain ⟨t, ht⟩ := hex
        obtain ⟨hIz, hJz, hXz, hLT, hLE, hG1, hG2, hBAD⟩ := ht
        set z : Power R 1 := fun _ => (Power.append y t)
          (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) with hzdef
        set w1 : Power R 1 := fun _ => (Power.append y t)
          (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) with hw1def
        set w2 : Power R 1 := fun _ => (Power.append y t)
          (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) with hw2def
        have eZt : (fun i : Fin 1 => (Power.append y t) (tCZ i)) = z := by
          funext i
          have hiv : i.val < 1 := i.isLt
          have hi0 : i.val = 0 := by omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          rfl
        have eT1t : (fun j : Fin (1 + 1) => (Power.append y t) (tG1 j))
            = Power.append y w1 := by
          funext j
          by_cases hj : j.val = 0
          · have e : tG1 j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tG1, hj]
            have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
            calc (Power.append y t) (tG1 j)
                = (Power.append y t) (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
              _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append y w1)
                  (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_left y w1 (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append y w1) j := by rw [hj0]
          · have e : tG1 j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tG1, hj]
            have hjv : j.val = 1 := by omega
            have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
            calc (Power.append y t) (tG1 j)
                = (Power.append y t) (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
              _ = w1 ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append y w1)
                  (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_right y w1 (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append y w1) j := by rw [hj1]
        have eT2t : (fun j : Fin (1 + 1) => (Power.append y t) (tG2 j))
            = Power.append z w2 := by
          funext j
          by_cases hj : j.val = 0
          · have e : tG2 j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tG2, hj]
            have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
            calc (Power.append y t) (tG2 j)
                = (Power.append y t) (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
              _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append z w2)
                  (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_left z w2 (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append z w2) j := by rw [hj0]
          · have e : tG2 j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tG2, hj]
            have hjv : j.val = 1 := by omega
            have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
            calc (Power.append y t) (tG2 j)
                = (Power.append y t) (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
              _ = w2 ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append z w2)
                  (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_right z w2 (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append z w2) j := by rw [hj1]
        have hzI : I z := by
          rw [← eZt]
          exact hIz
        have hzJ : openInterval a b z := by
          rw [← eZt]
          exact hJz
        have hyz : Lt1 y z := hLT
        have hzx : Lt1 z x₀ := by
          rw [eZt] at hXz
          obtain ⟨-, hlt1⟩ := hXz
          exact hlt1
        have hleYZ : LT.lt (Power.coord1 y) (Power.coord1 z) ∨
            Power.coord1 y = Power.coord1 z := by
          rcases hLE with hLT2 | hEQ
          · exact Or.inl hLT2
          · exact Or.inr hEQ
        have hGyw1 : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w1) := by
          rw [← eT1t]
          exact hG1
        have hGzw2 : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append z w2) := by
          rw [← eT2t]
          exact hG2
        have hval : Lt1 w1 (f.toFun (Subtype.mk z hzI)).1 :=
          hall z w1 hzI hzJ hyz hzx hleYZ hGyw1
        have eW : w2 = (f.toFun (Subtype.mk z hzI)).1 := by
          obtain ⟨hx0, heq0⟩ := hGzw2
          have eL0 : Power.left (Power.append z w2) = z := appendLeftAux _ _
          have eR0 : Power.right (Power.append z w2) = w2 := appendRightAux _ _
          calc w2 = Power.right (Power.append z w2) := eR0.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append z w2)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk z hzI)).1 := by simp only [eL0]
        rcases hBAD with hBADlt | hBADeq
        · have hLT2' : LT.lt (Power.coord1 w2) (Power.coord1 w1) := hBADlt
          have hval' : LT.lt (Power.coord1 w1)
              (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) := hval
          rw [eW] at hLT2'
          exact lt_irrefl _ (lt_trans hval' hLT2')
        · have heq' : Power.coord1 w1 = Power.coord1 w2 := hBADeq
          have hval' : LT.lt (Power.coord1 w1)
              (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) := hval
          rw [eW] at heq'
          rw [heq'] at hval'
          exact lt_irrefl _ hval'
  rw [← heqT]
  exact hTmem

open Monotonicity_Theorem

-- Difficult above_above case: uniform valleys are impossible for injective f.
-- Derive False via left-global minima, candidate suprema, and nested minima.
theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : ∀ x y (hx : I x) (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    {a b : Endpoint R} (hsubJ : ∀ x, openInterval a b x → I x)
    (hlt : Endpoint.lt a b)
    (hU : ∀ x (hxI : I x), openInterval a b x ->
        ∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
        Lt1 c1 x ∧ Lt1 x c2 ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 c1 y → Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 x y → Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) :
    ∃ a2 b2 : Endpoint R, Endpoint.lt a2 b2 ∧
      (∀ x, openInterval a2 b2 x → I x) ∧
      (∀ x (hxI : I x) y (hyI : I y), openInterval a2 b2 x → openInterval a2 b2 y ->
        Lt1 x y → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) := by
  by_cases hJne : (openInterval a b).Nonempty
  · -- Nonempty window: derive False.
    set L : Set (Power R 1) := fun x : Power R 1 => openInterval a b x ∧
      ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 y x ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) ->
        Lt1 v w with hLdef
    have hLmem : M.S 1 L := leftMinDefinable M f a b
    have hLfin : Set.Finite L := by
      by_contra hne
      have hInf : Set.Infinite L := hne
      obtain ⟨a', b', hltAB, hsubAB⟩ :=
        Monotonicity_Theorem.infinite_definable_set_contains_interval2 M L hLmem hInf
      have hJne' : (openInterval a' b').Nonempty := by
        cases a' with
        | negInf =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val =>
            obtain ⟨y, hym⟩ := exists_lt val
            exact ⟨fun _ => y, trivial, hym⟩
          | posInf =>
            have xJex : ∃ x : Power R 1, openInterval a b x := hJne
            obtain ⟨xJ, -⟩ := xJex
            exact ⟨xJ, trivial, trivial⟩
        | finite val =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val2 =>
            obtain ⟨y, hy1, hy2⟩ := exists_between hltAB
            exact ⟨fun _ => y, hy1, hy2⟩
          | posInf =>
            obtain ⟨y, hym⟩ := exists_gt val
            exact ⟨fun _ => y, hym, trivial⟩
        | posInf => exact False.elim hltAB
      obtain ⟨p, hp⟩ := hJne'
      obtain ⟨u, v, huv, hsubUV⟩ := finiteSubwindow hp
      have hsub : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval a b x := by
        intro x hx
        have hLx : L x := hsubAB (hsubUV x hx)
        exact hLx.left
      have hdec : ∀ x (hxI : I x) y (hyI : I y),
          openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval (Endpoint.finite u) (Endpoint.finite v) y ->
          Lt1 x y → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
        intro x hxI y hyI hjx hjy hxy
        have hyL : L y := hsubAB (hsubUV y hjy)
        have hyL' : openInterval a b y ∧
            (∀ y0 w v : Power R 1, I y0 → openInterval a b y0 → Lt1 y0 y ->
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append y0 w) ->
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append y v) ->
              Lt1 v w) := hyL
        have hallY : ∀ y0 w v : Power R 1, I y0 → openInterval a b y0 → Lt1 y0 y ->
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y0 w) ->
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y v) ->
            Lt1 v w := hyL'.right
        have hxJab : openInterval a b x := hsub _ hjx
        have hxI' : I x := hsubJ _ hxJab
        have eLx : Power.left (Power.append x ((f.toFun (Subtype.mk x hxI')).1)) = x :=
          appendLeftAux _ _
        have eRx : Power.right (Power.append x ((f.toFun (Subtype.mk x hxI')).1)) =
            (f.toFun (Subtype.mk x hxI')).1 :=
          appendRightAux _ _
        have hGx : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x ((f.toFun (Subtype.mk x hxI')).1)) :=
          ⟨eLx.symm ▸ hxI', by simp only [eLx, eRx]⟩
        have eLy : Power.left (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) = y :=
          appendLeftAux _ _
        have eRy : Power.right (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) =
            (f.toFun (Subtype.mk y hyI)).1 :=
          appendRightAux _ _
        have hGy : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) :=
          ⟨eLy.symm ▸ hyI, by simp only [eLy, eRy]⟩
        exact hallY x _ _ hxI' hxJab hxy hGx hGy
      exact Monotonicity_Theorem.incompatible_decreasing_above_above M f
        hsubJ hU huv hsub hdec
    -- Base right endpoint: min of L, or b if L is empty.
    have hLFin : Set.Finite L := hLfin
    set LF : Finset R := hLFin.toFinset.image Power.coord1 with hLFdef
    have hLFmp : ∀ x : Power R 1, L x → Power.coord1 x ∈ LF := by
      intro x hx
      rw [hLFdef]
      exact Finset.mem_image.mpr ⟨x, hLFin.mem_toFinset.mpr hx, rfl⟩
    have hLFmpr : ∀ c : R, c ∈ LF → ∃ x : Power R 1, L x ∧ Power.coord1 x = c := by
      intro c hc
      rw [hLFdef] at hc
      obtain ⟨x, hx, hcx⟩ := Finset.mem_image.mp hc
      exact ⟨x, hLFin.mem_toFinset.mp hx, hcx⟩
    have ha' : ∃ ap : Endpoint R, Endpoint.lt a ap ∧
        (∀ x, openInterval a ap x → x ∉ L) ∧
        (∀ x, openInterval a ap x → openInterval a b x) := by
      by_cases hLFempty : LF = ∅
      · refine ⟨b, hlt, ?_, ?_⟩
        · intro x hx hxL
          have hmem : Power.coord1 x ∈ LF := hLFmp x hxL
          rw [hLFempty] at hmem
          exact Finset.notMem_empty _ hmem
        · intro x hx
          exact hx
      · have hLFne : LF.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLFempty
        obtain ⟨m, hmMem, hmLe⟩ : ∃ m, m ∈ LF ∧ ∀ r ∈ LF, m ≤ r :=
          ⟨LF.min' hLFne, Finset.min'_mem LF hLFne, fun r hr => Finset.min'_le LF r hr⟩
        have hmLeast : ∀ r ∈ LF, LT.lt m r ∨ m = r :=
          fun r hr => lt_or_eq_of_le (hmLe r hr)
        obtain ⟨xstar, hxstarL, hcxstar⟩ := hLFmpr m hmMem
        have hweq : (fun _ => m) = xstar := by
          funext i
          have hi0 : i.val = 0 := by
            have := i.isLt
            omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          exact hcxstar.symm
        have hxStar : L (fun _ => m) := by
          rw [hweq]
          exact hxstarL
        have hJstar : openInterval a b (fun _ => m) := hxStar.left
        have ham' : Endpoint.lt a (Endpoint.finite m) := hJstar.left
        have hmb' : Endpoint.lt (Endpoint.finite m) b := hJstar.right
        refine ⟨Endpoint.finite m, ham', ?_, ?_⟩
        · intro x hx hxL
          have hmem : Power.coord1 x ∈ LF := hLFmp x hxL
          have hle := hmLeast (Power.coord1 x) hmem
          have hltxm : LT.lt (Power.coord1 x) m := hx.right
          rcases hle with h | h
          · exact lt_irrefl _ (lt_trans hltxm h)
          · rw [h] at hltxm
            exact lt_irrefl _ hltxm
        · intro x hx
          obtain ⟨hxlo, hxhi⟩ := hx
          refine ⟨hxlo, ?_⟩
          exact hiTrans b hmb' hxhi
    obtain ⟨ap, hapLt, hapNoL, hapSub⟩ := ha'
    -- Witness x₀ in (a, ap).
    have hAne : (openInterval a ap).Nonempty := by
      cases ap with
      | negInf =>
        cases a with
        | negInf => exact False.elim hapLt
        | finite _ => exact False.elim hapLt
        | posInf => exact False.elim hapLt
      | finite val =>
        cases a with
        | negInf =>
          obtain ⟨y, hym⟩ := exists_lt val
          exact ⟨fun _ => y, trivial, hym⟩
        | finite val2 =>
          have hlt2 : LT.lt val2 val := hapLt
          obtain ⟨y, hy1, hy2⟩ := exists_between hlt2
          exact ⟨fun _ => y, hy1, hy2⟩
        | posInf => exact False.elim hapLt
      | posInf =>
        obtain ⟨xJ, hxJ⟩ := hJne
        obtain ⟨hxlo, -⟩ := hxJ
        exact ⟨xJ, hxlo, trivial⟩
    obtain ⟨x₀, hx₀mem⟩ := hAne
    have hx₀J : openInterval a b x₀ := hapSub _ hx₀mem
    have hx₀nL : x₀ ∉ L := hapNoL _ hx₀mem
    have hx₀I : I x₀ := hsubJ _ hx₀J
    set v₀ : Power R 1 := (f.toFun (Subtype.mk x₀ hx₀I)).1 with hv₀def
    set S : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧
      Lt1 y x₀ ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w v₀) with hSdef
    -- S(x₀) is nonempty: x₀ is not a left-global minimum.
    have hNotAll : ¬ ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 y x₀ ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x₀ v) ->
        Lt1 v w := by
      intro hall
      apply hx₀nL
      rw [hLdef]
      exact ⟨hx₀J, hall⟩
    obtain ⟨y, hy1⟩ := Classical.not_forall.mp hNotAll
    obtain ⟨w, hw1⟩ := Classical.not_forall.mp hy1
    obtain ⟨v, hv1⟩ := Classical.not_forall.mp hw1
    have hyI : I y :=
      Classical.byContradiction (fun na => hv1 (fun a _ _ _ _ => absurd a na))
    have hyJ : openInterval a b y :=
      Classical.byContradiction (fun na => hv1 (fun _ a _ _ _ => absurd a na))
    have hyx : Lt1 y x₀ :=
      Classical.byContradiction (fun nb => hv1 (fun _ _ b _ _ => absurd b nb))
    have hGyw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y w) :=
      Classical.byContradiction (fun nc => hv1 (fun _ _ _ c _ => absurd c nc))
    have hGxv : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append x₀ v) :=
      Classical.byContradiction (fun nd => hv1 (fun _ _ _ _ d => absurd d nd))
    have hne : ¬ Lt1 v w :=
      fun he => hv1 (fun _ _ _ _ _ => he)
    have eW : w = (f.toFun (Subtype.mk y hyI)).1 := by
      obtain ⟨hx0, heq0⟩ := hGyw
      have eL : Power.left (Power.append y w) = y := appendLeftAux _ _
      have eR : Power.right (Power.append y w) = w := appendRightAux _ _
      calc w = Power.right (Power.append y w) := eR.symm
        _ = (f.toFun (Subtype.mk (Power.left (Power.append y w)) hx0)).1 := heq0
        _ = (f.toFun (Subtype.mk y hyI)).1 := by simp only [eL]
    have eV : v = (f.toFun (Subtype.mk x₀ hx₀I)).1 := by
      obtain ⟨hx0, heq0⟩ := hGxv
      have eL : Power.left (Power.append x₀ v) = x₀ := appendLeftAux _ _
      have eR : Power.right (Power.append x₀ v) = v := appendRightAux _ _
      calc v = Power.right (Power.append x₀ v) := eR.symm
        _ = (f.toFun (Subtype.mk (Power.left (Power.append x₀ v)) hx0)).1 := heq0
        _ = (f.toFun (Subtype.mk x₀ hx₀I)).1 := by simp only [eL]
    have hltYX : Lt1 (f.toFun (Subtype.mk y hyI)).1 v₀ := by
      have hne' : ¬ Lt1 v₀ (f.toFun (Subtype.mk y hyI)).1 := by
        rw [hv₀def, ← eV, ← eW]
        exact hne
      rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk y hyI)).1))
          (Power.coord1 v₀) with h | h | h
      · exact h
      · have heq := h
        have hval : (f.toFun (Subtype.mk y hyI)).1 = v₀ := by
          funext i
          have hiv : i.val < 1 := i.isLt
          have hi0 : i.val = 0 := by omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          exact heq
        have hsub : (f.toFun (Subtype.mk y hyI)) = (f.toFun (Subtype.mk x₀ hx₀I)) :=
          Subtype.ext hval
        have heqYX : y = x₀ := hinj y x₀ hyI hx₀I hsub
        have hcon : Lt1 x₀ x₀ := heqYX ▸ hyx
        exact False.elim (lt_irrefl _ hcon)
      · exact False.elim (hne' h)
    have hSwit : S y := by
      rw [hSdef]
      have eLy : Power.left (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) = y :=
        appendLeftAux _ _
      have eRy : Power.right (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) =
          (f.toFun (Subtype.mk y hyI)).1 :=
        appendRightAux _ _
      have hGyw' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) :=
        ⟨eLy.symm ▸ hyI, by simp only [eLy, eRy]⟩
      exact ⟨hyJ, hyx, (f.toFun (Subtype.mk y hyI)).1, hGyw', hltYX⟩
    have hSmem : M.S 1 S := belowPreimageDefinable M f a b x₀ hx₀I
    have hSne : S.Nonempty := ⟨y, hSwit⟩
    have hBnd : BoundedAbove1 S := by
      refine ⟨Power.coord1 x₀, ?_⟩
      intro s hs
      rw [hSdef] at hs
      obtain ⟨-, hlt, -⟩ := hs
      exact Or.inl hlt
    have hSup := supCompletenessAux S ((M.ominimal _).mp hSmem) hSne hBnd
    obtain ⟨m₁, hUBm, hLeastm⟩ := hSup
    -- m₁ is strictly left of x₀ (S avoids the left window).
    obtain ⟨c1x, c2x, hc1Jx, hc2Jx, hc1x, hxx2, hleftx, hrightx⟩ :=
      hU x₀ hx₀I hx₀J
    have hmc1x : LT.lt (Power.coord1 c1x) (Power.coord1 x₀) := hc1x
    have hc1UB : IsUpperBound1 S (Power.coord1 c1x) := by
      intro s hs
      rw [hSdef] at hs
      obtain ⟨hsJ, hsx, hsW⟩ := hs
      obtain ⟨w, hGw, hwlt⟩ := hsW
      rcases lt_trichotomy (Power.coord1 c1x) (Power.coord1 s) with h | h | h
      · have hlt1 := h
        exfalso
        have hsJab : openInterval a b s := hsJ
        have hsI : I s := hsubJ _ hsJab
        have hsc1 : Lt1 c1x s := hlt1
        have hsx0 : Lt1 s x₀ := hsx
        have hwin : Lt1 v₀ (f.toFun (Subtype.mk s hsI)).1 :=
          hleftx s hsI hsJab hsc1 hsx0
        have hval : Lt1 (f.toFun (Subtype.mk s hsI)).1 v₀ := by
          have eW : w = (f.toFun (Subtype.mk s hsI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append s w) = s := appendLeftAux _ _
            have eR : Power.right (Power.append s w) = w := appendRightAux _ _
            calc w = Power.right (Power.append s w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append s w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk s hsI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hwin hval)
      · have heq := h
        exact Or.inr heq.symm
      · have hlt2 := h
        exact Or.inl hlt2
    have hmUBc1 : LT.lt m₁ (Power.coord1 c1x) ∨ m₁ = Power.coord1 c1x :=
      hLeastm _ hc1UB
    have hmX : LT.lt m₁ (Power.coord1 x₀) := by
      rcases hmUBc1 with h | h
      · exact lt_trans h hmc1x
      · rw [h]
        exact hmc1x
    have hmJ : openInterval a b (fun _ => m₁) := by
      obtain ⟨s0, hs0⟩ := hSne
      have hs0' : openInterval a b s0 ∧ Lt1 s0 x₀ ∧
          (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
            (A := I) (B := B) f.toFun (Power.append s0 w) ∧
            Lt1 w v₀) := by
        rw [hSdef] at hs0
        exact hs0
      obtain ⟨hs0J, hs0x, -⟩ := hs0'
      have hs0le : LT.lt (Power.coord1 s0) m₁ ∨ Power.coord1 s0 = m₁ :=
        hUBm s0 hs0
      have haM : Endpoint.lt a (Endpoint.finite m₁) := by
        rcases hs0le with h | h
        · exact loTrans a hs0J.left h
        · rw [← h]
          exact hs0J.left
      have hMb : Endpoint.lt (Endpoint.finite m₁) b :=
        hiTrans b hx₀J.right hmX
      exact ⟨haM, hMb⟩
    have hmI : I (fun _ => m₁) := hsubJ _ hmJ
    obtain ⟨c1m, c2m, hc1Jm, hc2Jm, hc1m, hxm2, hleftm, hrightm⟩ :=
      hU (fun _ => m₁) hmI hmJ
    -- f(m₁) < f(x₀): else the left window at m₁ contradicts maximality.
    have hfmX : Lt1 (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 v₀ := by
      by_contra hne
      have hgt : Lt1 v₀ (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 := by
        rcases lt_trichotomy (Power.coord1 v₀)
            (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁) hmI)).1)) with h | h | h
        · exact h
        · have heq := h
          exfalso
          have hval : (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 =
              (f.toFun (Subtype.mk x₀ hx₀I)).1 := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            exact heq.symm
          have hsub : (f.toFun (Subtype.mk (fun _ => m₁) hmI)) =
              (f.toFun (Subtype.mk x₀ hx₀I)) :=
            Subtype.ext hval
          have heqM : (fun _ => m₁) = x₀ := hinj _ _ hmI hx₀I hsub
          have hcon2 : m₁ = Power.coord1 x₀ :=
            Eq.trans rfl (congrArg Power.coord1 heqM)
          rw [hcon2] at hmX
          exact lt_irrefl _ hmX
        · exact False.elim (hne h)
      obtain ⟨c1m, c2m, hc1Jm, hc2Jm, hc1m, hxm2, hleftm, hrightm⟩ :=
        hU (fun _ => m₁) hmI hmJ
      have hmc1 : LT.lt (Power.coord1 c1m) m₁ := hc1m
      obtain ⟨sp, hspA, hsppt⟩ := notUBofLeast S m₁ hLeastm (Power.coord1 c1m) hmc1
      -- sp ∈ S above c1m; sp ≤ m₁; case split
      have hsppm : LT.lt (Power.coord1 sp) m₁ ∨ Power.coord1 sp = m₁ :=
        hUBm sp hspA
      have hspJ : openInterval a b sp := by
        have hspA' : openInterval a b sp ∧ Lt1 sp x₀ ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append sp w) ∧
              Lt1 w v₀) := hspA
        exact hspA'.left
      have hspI : I sp := hsubJ _ hspJ
      have hleSP : LT.lt (Power.coord1 c1m) (Power.coord1 sp) := hsppt
      rcases hsppm with h | h
      · -- sp < m₁: left window gives f(m̂) < f(sp), but sp ∈ S gives f(sp) < f(x₀) < f(m̂).
        have hc1sp : Lt1 c1m sp := hleSP
        have hspm : Lt1 sp (fun _ => m₁) := h
        have hfmsp : Lt1 (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1
            (f.toFun (Subtype.mk sp hspI)).1 :=
          hleftm sp hspI hspJ hc1sp hspm
        have hspS : openInterval a b sp ∧ Lt1 sp x₀ ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append sp w) ∧
              Lt1 w v₀) := hspA
        obtain ⟨-, hspx, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have hspx0 : Lt1 sp x₀ := hspx
        have hfx : Lt1 (f.toFun (Subtype.mk sp hspI)).1 v₀ := by
          have eW : w = (f.toFun (Subtype.mk sp hspI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append sp w) = sp := appendLeftAux _ _
            have eR : Power.right (Power.append sp w) = w := appendRightAux _ _
            calc w = Power.right (Power.append sp w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append sp w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk sp hspI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hgt (lt_trans hfmsp hfx))
      · -- sp = m₁ (coords): then sp ∈ S gives f(m̂) < f(x₀), contra hgt.
        have ept : sp = (fun _ => m₁) := ptEqAux h
        subst ept
        have hspS : openInterval a b (fun _ => m₁) ∧ Lt1 (fun _ => m₁) x₀ ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append (fun _ => m₁) w) ∧
              Lt1 w v₀) := hspA
        obtain ⟨-, -, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have eW : w = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1 := by
          obtain ⟨hx0, heq0⟩ := hGw
          have eL : Power.left (Power.append (fun _ : Fin 1 => m₁) w) = (fun _ : Fin 1 => m₁) :=
            appendLeftAux _ _
          have eR : Power.right (Power.append (fun _ : Fin 1 => m₁) w) = w := appendRightAux _ _
          calc w = Power.right (Power.append (fun _ : Fin 1 => m₁) w) := eR.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => m₁) w)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1 := by simp only [eL]
        rw [eW] at hwlt
        exact lt_irrefl _ (lt_trans hgt hwlt)
    -- m₁ is a candidate for x₀.
    set T₀ : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧ Lt1 y x₀ ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
      (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
        Lt1 y z → Lt1 z x₀ →
        (LT.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) with hTdef
    have hTmem : M.S 1 T₀ := candDefinable M f a b x₀ hx₀I
    have hmT : T₀ (fun _ => m₁) := by
      rw [hTdef]
      have eLm : Power.left (Power.append (fun _ : Fin 1 => m₁)
          ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1)) = (fun _ : Fin 1 => m₁) :=
        appendLeftAux _ _
      have eRm : Power.right (Power.append (fun _ : Fin 1 => m₁)
          ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1)) =
          (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1 :=
        appendRightAux _ _
      have hGm : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ : Fin 1 => m₁) ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1)) :=
        ⟨eLm.symm ▸ hmI, by simp only [eLm, eRm]⟩
      refine ⟨hmJ, ?_, ?_, ?_⟩
      · exact hmX
      · exact ⟨(f.toFun (Subtype.mk (fun _ => m₁) hmI)).1, hGm, hfmX⟩
      · intro z w1 hzI hzJ hyz hzx hle hGyw1
        have eW1 : w1 = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1 := by
          obtain ⟨hx0, heq0⟩ := hGyw1
          have eL : Power.left (Power.append (fun _ : Fin 1 => m₁) w1) = (fun _ : Fin 1 => m₁) :=
            appendLeftAux _ _
          have eR : Power.right (Power.append (fun _ : Fin 1 => m₁) w1) = w1 :=
            appendRightAux _ _
          calc w1 = Power.right (Power.append (fun _ : Fin 1 => m₁) w1) := eR.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => m₁) w1)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1 := by simp only [eL]
        have hzx0 : Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 (f.toFun (Subtype.mk z hzI)).1 := by
          by_contra hne
          rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
              (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)) with h | h | h
          · have hzS : S z := by
              rw [hSdef]
              have eLz : Power.left (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) = z :=
                appendLeftAux _ _
              have eRz : Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) =
                  (f.toFun (Subtype.mk z hzI)).1 :=
                appendRightAux _ _
              have hGz : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) :=
                ⟨eLz.symm ▸ hzI, by simp only [eLz, eRz]⟩
              exact ⟨hzJ, hzx, (f.toFun (Subtype.mk z hzI)).1, hGz, h⟩
            have hzUB : LT.lt (Power.coord1 z) m₁ ∨ Power.coord1 z = m₁ :=
              hUBm z hzS
            have hzm : Lt1 (fun _ => m₁) z := hyz
            rcases hzUB with h2 | h2
            · exact lt_irrefl _ (lt_trans hzm h2)
            · have hzm' : LT.lt m₁ (Power.coord1 z) := hzm
              rw [h2] at hzm'
              exact lt_irrefl _ hzm'
          · have heq := h
            exfalso
            have hval : (f.toFun (Subtype.mk z hzI)).1 =
                (f.toFun (Subtype.mk x₀ hx₀I)).1 := by
              funext i
              have hiv : i.val < 1 := i.isLt
              have hi0 : i.val = 0 := by omega
              have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
              rw [hi]
              exact heq
            have hsub : (f.toFun (Subtype.mk z hzI)) = (f.toFun (Subtype.mk x₀ hx₀I)) :=
              Subtype.ext hval
            have heqZX : z = x₀ := hinj z x₀ hzI hx₀I hsub
            have hcon : Lt1 x₀ x₀ := heqZX ▸ hzx
            exact lt_irrefl _ hcon
          · exact False.elim (hne h)
        have hgoal : Lt1 w1 (f.toFun (Subtype.mk z hzI)).1 := by
          rw [eW1]
          exact lt_trans hfmX hzx0
        exact hgoal
    -- T₀ is finite: an interval inside would be increasing, contradicting valleys.
    have hTfin : Set.Finite T₀ := by
      by_contra hne
      have hInf : Set.Infinite T₀ := hne
      obtain ⟨a', b', hltAB, hsubAB⟩ :=
        Monotonicity_Theorem.infinite_definable_set_contains_interval2 M T₀ hTmem hInf
      have hTne : T₀.Nonempty := ⟨_, hmT⟩
      have hJne' : (openInterval a' b').Nonempty := by
        cases a' with
        | negInf =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val =>
            obtain ⟨y, hym⟩ := exists_lt val
            exact ⟨fun _ => y, trivial, hym⟩
          | posInf =>
            obtain ⟨s0, hs0⟩ := hTne
            exact ⟨s0, trivial, trivial⟩
        | finite val =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val2 =>
            have hlt2 : LT.lt val val2 := hltAB
            obtain ⟨y, hy1, hy2⟩ := exists_between hlt2
            exact ⟨fun _ => y, hy1, hy2⟩
          | posInf =>
            obtain ⟨y, hym⟩ := exists_gt val
            exact ⟨fun _ => y, hym, trivial⟩
        | posInf => exact False.elim hltAB
      obtain ⟨p, hp⟩ := hJne'
      obtain ⟨u, v, huv, hsubUV⟩ := finiteSubwindow hp
      have hinc : ∀ x (hxI : I x) y (hyI : I y),
          openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval (Endpoint.finite u) (Endpoint.finite v) y ->
          Lt1 x y → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
        intro x hxI y hyI hjx hjy hxy
        have hxT : T₀ x := hsubAB (hsubUV x hjx)
        have hxT' : openInterval a b x ∧ Lt1 x x₀ ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append x w) ∧
              Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
            (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
              Lt1 x z → Lt1 z x₀ →
              (LT.lt (Power.coord1 x) (Power.coord1 z) ∨ Power.coord1 x = Power.coord1 z) →
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x w1) →
              Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) := hxT
        obtain ⟨-, -, -, hxU⟩ := hxT'
        have hyJ : openInterval a b y := by
          have hyT : T₀ y := hsubAB (hsubUV y hjy)
          have hyT' : openInterval a b y ∧ Lt1 y x₀ ∧
              (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                (A := I) (B := B) f.toFun (Power.append y w) ∧
                Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
              (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
                Lt1 y z → Lt1 z x₀ →
                (LT.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append y w1) →
                Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) := hyT
          exact hyT'.left
        have hyI' : I y := hsubJ _ hyJ
        have hyx0 : Lt1 y x₀ := by
          have hyTy : T₀ y := hsubAB (hsubUV y hjy)
          have hyT' : openInterval a b y ∧ Lt1 y x₀ ∧
              (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                (A := I) (B := B) f.toFun (Power.append y w) ∧
                Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
              (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
                Lt1 y z → Lt1 z x₀ →
                (LT.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append y w1) →
                Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) := hyTy
          exact hyT'.right.left
        have eLx : Power.left (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) = x :=
          appendLeftAux _ _
        have eRx : Power.right (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) =
            (f.toFun (Subtype.mk x hxI)).1 :=
          appendRightAux _ _
        have hGx : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) :=
          ⟨eLx.symm ▸ hxI, by simp only [eLx, eRx]⟩
        have hleXY : LT.lt (Power.coord1 x) (Power.coord1 y) ∨
            Power.coord1 x = Power.coord1 y := Or.inl hxy
        exact hxU y _ hyI' hyJ hxy hyx0 hleXY hGx
      have hsub : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval a b x := by
        intro x hx
        have hxT : T₀ x := hsubAB (hsubUV x hx)
        have hxT' : openInterval a b x ∧ Lt1 x x₀ ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append x w) ∧
              Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
            (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
              Lt1 x z → Lt1 z x₀ →
              (LT.lt (Power.coord1 x) (Power.coord1 z) ∨ Power.coord1 x = Power.coord1 z) →
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x w1) →
              Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) := hxT
        exact hxT'.left
      exact Monotonicity_Theorem.incompatible_increasing_above_above M f
        hsubJ hU huv hsub hinc
    -- Least candidate of T₀.
    have hTFin : Set.Finite T₀ := hTfin
    set TF : Finset R := hTFin.toFinset.image Power.coord1 with hTFdef
    have hTFmp : ∀ x : Power R 1, T₀ x → Power.coord1 x ∈ TF := by
      intro x hx
      rw [hTFdef]
      exact Finset.mem_image.mpr ⟨x, hTFin.mem_toFinset.mpr hx, rfl⟩
    have hTFmpr : ∀ c : R, c ∈ TF → ∃ x : Power R 1, T₀ x ∧ Power.coord1 x = c := by
      intro c hc
      rw [hTFdef] at hc
      obtain ⟨x, hx, hcx⟩ := Finset.mem_image.mp hc
      exact ⟨x, hTFin.mem_toFinset.mp hx, hcx⟩
    have hTne : T₀.Nonempty := ⟨_, hmT⟩
    obtain ⟨s0, hs0⟩ := hTne
    have hTFne : TF.Nonempty := ⟨Power.coord1 s0, hTFmp s0 hs0⟩
    obtain ⟨t₁, ht1Mem, ht1Le⟩ : ∃ t, t ∈ TF ∧ ∀ r ∈ TF, t ≤ r :=
      ⟨TF.min' hTFne, Finset.min'_mem TF hTFne, fun r hr => Finset.min'_le TF r hr⟩
    have ht1Least : ∀ r ∈ TF, LT.lt t₁ r ∨ t₁ = r :=
      fun r hr => lt_or_eq_of_le (ht1Le r hr)
    obtain ⟨xstar, hxstarT, hcxtstar⟩ := hTFmpr t₁ ht1Mem
    have hweqT : (fun _ => t₁) = xstar := by
      funext i
      have hi0 : i.val = 0 := by
        have := i.isLt
        omega
      have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
      rw [hi]
      exact hcxtstar.symm
    have ht1T : T₀ (fun _ => t₁) := by
      rw [hweqT]
      exact hxstarT
    have ht1J : openInterval a b (fun _ => t₁) := ht1T.left
    have ht1x : Lt1 (fun _ => t₁) x₀ := ht1T.right.left
    have ht1I : I (fun _ => t₁) := hsubJ _ ht1J
    have ht1ap : openInterval a ap (fun _ => t₁) := by
      refine ⟨ht1J.left, ?_⟩
      exact hiTrans ap hx₀mem.right ht1x
    have ht1nL : (fun _ => t₁) ∉ L := hapNoL _ ht1ap
    have ht1I : I (fun _ => t₁) := hsubJ _ ht1J
    set v₁ : Power R 1 := (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 with hv₁def
    set S₁ : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧
      Lt1 y (fun _ => t₁) ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w v₁) with hS₁def
    -- S(t₁) is nonempty.
    have hNotAll₁ : ¬ ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 y (fun _ => t₁) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => t₁) v) ->
        Lt1 v w := by
      intro hall
      apply ht1nL
      rw [hLdef]
      exact ⟨ht1J, hall⟩
    obtain ⟨y₂, hy1₂⟩ := Classical.not_forall.mp hNotAll₁
    obtain ⟨w₂, hw1₂⟩ := Classical.not_forall.mp hy1₂
    obtain ⟨v₂, hv1₂⟩ := Classical.not_forall.mp hw1₂
    have hyI₂ : I y₂ :=
      Classical.byContradiction (fun na => hv1₂ (fun a _ _ _ _ => absurd a na))
    have hyJ₂ : openInterval a b y₂ :=
      Classical.byContradiction (fun na => hv1₂ (fun _ a _ _ _ => absurd a na))
    have hyx₂ : Lt1 y₂ (fun _ => t₁) :=
      Classical.byContradiction (fun nb => hv1₂ (fun _ _ b _ _ => absurd b nb))
    have hGyw₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y₂ w₂) :=
      Classical.byContradiction (fun nc => hv1₂ (fun _ _ _ c _ => absurd c nc))
    have hGxv₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append (fun _ => t₁) v₂) :=
      Classical.byContradiction (fun nd => hv1₂ (fun _ _ _ _ d => absurd d nd))
    have hne₂ : ¬ Lt1 v₂ w₂ :=
      fun he => hv1₂ (fun _ _ _ _ _ => he)
    have eW₂ : w₂ = (f.toFun (Subtype.mk y₂ hyI₂)).1 := by
      obtain ⟨hx0, heq0⟩ := hGyw₂
      have eL : Power.left (Power.append y₂ w₂) = y₂ := appendLeftAux _ _
      have eR : Power.right (Power.append y₂ w₂) = w₂ := appendRightAux _ _
      calc w₂ = Power.right (Power.append y₂ w₂) := eR.symm
        _ = (f.toFun (Subtype.mk (Power.left (Power.append y₂ w₂)) hx0)).1 := heq0
        _ = (f.toFun (Subtype.mk y₂ hyI₂)).1 := by simp only [eL]
    have eV₂ : v₂ = (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := by
      obtain ⟨hx0, heq0⟩ := hGxv₂
      have eL : Power.left (Power.append (fun _ : Fin 1 => t₁) v₂) = (fun _ : Fin 1 => t₁) :=
        appendLeftAux _ _
      have eR : Power.right (Power.append (fun _ : Fin 1 => t₁) v₂) = v₂ := appendRightAux _ _
      calc v₂ = Power.right (Power.append (fun _ : Fin 1 => t₁) v₂) := eR.symm
        _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => t₁) v₂)) hx0)).1 := heq0
        _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => t₁) ht1I)).1 := by simp only [eL]
    have hltYX₂ : Lt1 (f.toFun (Subtype.mk y₂ hyI₂)).1 v₁ := by
      have hne₂' : ¬ Lt1 v₁ (f.toFun (Subtype.mk y₂ hyI₂)).1 := by
        rw [hv₁def, ← eV₂, ← eW₂]
        exact hne₂
      rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk y₂ hyI₂)).1))
          (Power.coord1 v₁) with h | h | h
      · exact h
      · have heq := h
        exfalso
        have hval : (f.toFun (Subtype.mk y₂ hyI₂)).1 = v₁ := by
          funext i
          have hiv : i.val < 1 := i.isLt
          have hi0 : i.val = 0 := by omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          exact heq
        have hsub : (f.toFun (Subtype.mk y₂ hyI₂)) = (f.toFun (Subtype.mk (fun _ => t₁) ht1I)) :=
          Subtype.ext hval
        have heqYX : y₂ = (fun _ => t₁) := hinj y₂ _ hyI₂ ht1I hsub
        have hcon : Lt1 (fun _ => t₁) (fun _ => t₁) := heqYX ▸ hyx₂
        exact lt_irrefl _ hcon
      · exact False.elim (hne₂' h)
    have hSwit₂ : S₁ y₂ := by
      rw [hS₁def]
      have eLy : Power.left (Power.append y₂ ((f.toFun (Subtype.mk y₂ hyI₂)).1)) = y₂ :=
        appendLeftAux _ _
      have eRy : Power.right (Power.append y₂ ((f.toFun (Subtype.mk y₂ hyI₂)).1)) =
          (f.toFun (Subtype.mk y₂ hyI₂)).1 :=
        appendRightAux _ _
      have hGyw' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y₂ ((f.toFun (Subtype.mk y₂ hyI₂)).1)) :=
        ⟨eLy.symm ▸ hyI₂, by simp only [eLy, eRy]⟩
      exact ⟨hyJ₂, hyx₂, (f.toFun (Subtype.mk y₂ hyI₂)).1, hGyw', hltYX₂⟩
    have hSmem₁ : M.S 1 S₁ := belowPreimageDefinable M f a b (fun _ => t₁) ht1I
    have hSne₁ : S₁.Nonempty := ⟨y₂, hSwit₂⟩
    have hBnd₁ : BoundedAbove1 S₁ := by
      refine ⟨t₁, ?_⟩
      intro s hs
      rw [hS₁def] at hs
      obtain ⟨-, hlt, -⟩ := hs
      exact Or.inl hlt
    have hSup₁ := supCompletenessAux S₁ ((M.ominimal _).mp hSmem₁) hSne₁ hBnd₁
    obtain ⟨m₁', hUBm', hLeastm'⟩ := hSup₁
    obtain ⟨c1t, c2t, hc1Jt, hc2Jt, hc1t, hxt2, hleftt, hrightt⟩ :=
      hU (fun _ => t₁) ht1I ht1J
    have hmc1t : LT.lt (Power.coord1 c1t) t₁ := hc1t
    have hc1UB' : IsUpperBound1 S₁ (Power.coord1 c1t) := by
      intro s hs
      rw [hS₁def] at hs
      obtain ⟨hsJ, hsx, hsW⟩ := hs
      obtain ⟨w, hGw, hwlt⟩ := hsW
      rcases lt_trichotomy (Power.coord1 c1t) (Power.coord1 s) with h | h | h
      · have hlt1 := h
        exfalso
        have hsJab : openInterval a b s := hsJ
        have hsI : I s := hsubJ _ hsJab
        have hsc1 : Lt1 c1t s := hlt1
        have hsxt : Lt1 s (fun _ => t₁) := hsx
        have hwin : Lt1 v₁ (f.toFun (Subtype.mk s hsI)).1 :=
          hleftt s hsI hsJab hsc1 hsxt
        have hval : Lt1 (f.toFun (Subtype.mk s hsI)).1 v₁ := by
          have eW : w = (f.toFun (Subtype.mk s hsI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append s w) = s := appendLeftAux _ _
            have eR : Power.right (Power.append s w) = w := appendRightAux _ _
            calc w = Power.right (Power.append s w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append s w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk s hsI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hwin hval)
      · have heq := h
        exact Or.inr heq.symm
      · have hlt2 := h
        exact Or.inl hlt2
    have hmUBc1' : LT.lt m₁' (Power.coord1 c1t) ∨ m₁' = Power.coord1 c1t :=
      hLeastm' _ hc1UB'
    have hmX' : LT.lt m₁' t₁ := by
      rcases hmUBc1' with h | h
      · exact lt_trans h hmc1t
      · rw [h]
        exact hmc1t
    have hmJ' : openInterval a b (fun _ => m₁') := by
      obtain ⟨s0, hs0⟩ := hSne₁
      have hs0' : openInterval a b s0 ∧ Lt1 s0 (fun _ => t₁) ∧
          (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
            (A := I) (B := B) f.toFun (Power.append s0 w) ∧
            Lt1 w v₁) := by
        rw [hS₁def] at hs0
        exact hs0
      obtain ⟨hs0J, hs0x, -⟩ := hs0'
      have hs0le : LT.lt (Power.coord1 s0) m₁' ∨ Power.coord1 s0 = m₁' :=
        hUBm' s0 hs0
      have haM : Endpoint.lt a (Endpoint.finite m₁') := by
        rcases hs0le with h | h
        · exact loTrans a hs0J.left h
        · rw [← h]
          exact hs0J.left
      have hMb : Endpoint.lt (Endpoint.finite m₁') b :=
        hiTrans b ht1J.right hmX'
      exact ⟨haM, hMb⟩
    have hmI' : I (fun _ => m₁') := hsubJ _ hmJ'
    obtain ⟨c1m', c2m', hc1Jm', hc2Jm', hc1m', hxm2', hleftm', hrightm'⟩ :=
      hU (fun _ => m₁') hmI' hmJ'
    have hfmX' : Lt1 (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 v₁ := by
      by_contra hne
      have hgt : Lt1 v₁ (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 := by
        rcases lt_trichotomy (Power.coord1 v₁)
            (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁') hmI')).1)) with h | h | h
        · exact h
        · have heq := h
          exfalso
          have hval : (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 =
              (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            exact heq.symm
          have hsub : (f.toFun (Subtype.mk (fun _ => m₁') hmI')) =
              (f.toFun (Subtype.mk (fun _ => t₁) ht1I)) :=
            Subtype.ext hval
          have heqM : (fun _ => m₁') = (fun _ => t₁) := hinj _ _ hmI' ht1I hsub
          have hcon2 : m₁' = t₁ :=
            Eq.trans rfl (congrArg Power.coord1 heqM)
          rw [hcon2] at hmX'
          exact lt_irrefl _ hmX'
        · exact False.elim (hne h)
      have hmc1' : LT.lt (Power.coord1 c1m') m₁' := hc1m'
      obtain ⟨spp, hsppA, hsppt⟩ := notUBofLeast S₁ m₁' hLeastm' (Power.coord1 c1m') hmc1'
      have hsppm : LT.lt (Power.coord1 spp) m₁' ∨ Power.coord1 spp = m₁' :=
        hUBm' spp hsppA
      have hspJ : openInterval a b spp := by
        have hspA' : openInterval a b spp ∧ Lt1 spp (fun _ => t₁) ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append spp w) ∧
              Lt1 w v₁) := hsppA
        exact hspA'.left
      have hspI : I spp := hsubJ _ hspJ
      rcases hsppm with h | h
      · -- sp < m₁': left window gives f(m̂') < f(sp), but sp ∈ S gives f(sp) < f(t₁) < f(m̂').
        have hc1sp : Lt1 c1m' spp := hsppt
        -- hsppt : LT.lt c1c spc. hc1sp needs Lt1 c1m' spp ≡ LT.lt c1c spc ✓ defeq. `exact hsppt`? hsppt : LT.lt (coord c1m') (coord spp). Goal Lt1 c1m' spp ≡ same ✓. So `have hc1sp : ... := hsppt`.
        have hspm : Lt1 spp (fun _ => m₁') := h
        have hfmsp : Lt1 (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1
            (f.toFun (Subtype.mk spp hspI)).1 :=
          hleftm' spp hspI hspJ hc1sp hspm
        have hspS : openInterval a b spp ∧ Lt1 spp (fun _ => t₁) ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append spp w) ∧
              Lt1 w v₁) := hsppA
        obtain ⟨-, hspx, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have hfx : Lt1 (f.toFun (Subtype.mk spp hspI)).1 v₁ := by
          have eW : w = (f.toFun (Subtype.mk spp hspI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append spp w) = spp := appendLeftAux _ _
            have eR : Power.right (Power.append spp w) = w := appendRightAux _ _
            calc w = Power.right (Power.append spp w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append spp w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk spp hspI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hgt (lt_trans hfmsp hfx))
      · -- sp = m₁' (coords): then sp ∈ S gives f(m̂') < f(t₁), contra hgt.
        have ept : spp = (fun _ => m₁') := ptEqAux h
        subst ept
        have hspS : openInterval a b (fun _ => m₁') ∧ Lt1 (fun _ => m₁') (fun _ => t₁) ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append (fun _ => m₁') w) ∧
              Lt1 w v₁) := hsppA
        obtain ⟨-, -, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have eW : w = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 := by
          obtain ⟨hx0, heq0⟩ := hGw
          have eL : Power.left (Power.append (fun _ : Fin 1 => m₁') w) = (fun _ : Fin 1 => m₁') :=
            appendLeftAux _ _
          have eR : Power.right (Power.append (fun _ : Fin 1 => m₁') w) = w := appendRightAux _ _
          calc w = Power.right (Power.append (fun _ : Fin 1 => m₁') w) := eR.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => m₁') w)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 := by simp only [eL]
        rw [eW] at hwlt
        exact lt_irrefl _ (lt_trans hgt hwlt)
    -- m₁' is a candidate for t₁.
    set T₁ : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧ Lt1 y (fun _ => t₁) ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 w (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1) ∧
      (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
        Lt1 y z → Lt1 z (fun _ => t₁) →
        (LT.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) with hT₁def
    have hT₁mem : M.S 1 T₁ := candDefinable M f a b (fun _ => t₁) ht1I
    have hm₁'T₁ : T₁ (fun _ => m₁') := by
      rw [hT₁def]
      have eLm : Power.left (Power.append (fun _ : Fin 1 => m₁')
          ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) = (fun _ : Fin 1 => m₁') :=
        appendLeftAux _ _
      have eRm : Power.right (Power.append (fun _ : Fin 1 => m₁')
          ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) =
          (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 :=
        appendRightAux _ _
      have hGm : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ : Fin 1 => m₁') ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) :=
        ⟨eLm.symm ▸ hmI', by simp only [eLm, eRm]⟩
      have hxmM : Lt1 (fun _ => m₁') (fun _ => t₁) := hmX'
      refine ⟨hmJ', ?_, ?_, ?_⟩
      · exact hmX'
      · exact ⟨(f.toFun (Subtype.mk (fun _ => m₁') hmI')).1, hGm, hfmX'⟩
      · intro z w1 hzI hzJ hyz hzx hle hGyw1
        have eW1 : w1 = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 := by
          obtain ⟨hx0, heq0⟩ := hGyw1
          have eL : Power.left (Power.append (fun _ : Fin 1 => m₁') w1) = (fun _ : Fin 1 => m₁') :=
            appendLeftAux _ _
          have eR : Power.right (Power.append (fun _ : Fin 1 => m₁') w1) = w1 :=
            appendRightAux _ _
          calc w1 = Power.right (Power.append (fun _ : Fin 1 => m₁') w1) := eR.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => m₁') w1)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 := by simp only [eL]
        have hzt1 : Lt1 (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1
            (f.toFun (Subtype.mk z hzI)).1 := by
          by_contra hne
          rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
              (Power.coord1 ((f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1)) with h | h | h
          · have hzS : S₁ z := by
              rw [hS₁def]
              have eLz : Power.left (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) = z :=
                appendLeftAux _ _
              have eRz : Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) =
                  (f.toFun (Subtype.mk z hzI)).1 :=
                appendRightAux _ _
              have hGz : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) :=
                ⟨eLz.symm ▸ hzI, by simp only [eLz, eRz]⟩
              exact ⟨hzJ, hzx, _, hGz, h⟩
            have hzUB : LT.lt (Power.coord1 z) m₁' ∨ Power.coord1 z = m₁' :=
              hUBm' z hzS
            have hzm : Lt1 (fun _ => m₁') z := hyz
            rcases hzUB with h2 | h2
            · exact lt_irrefl _ (lt_trans hzm h2)
            · have hzm' : LT.lt m₁' (Power.coord1 z) := hzm
              rw [h2] at hzm'
              exact lt_irrefl _ hzm'
          · have heq := h
            exfalso
            have hval : (f.toFun (Subtype.mk z hzI)).1 =
                (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := by
              funext i
              have hiv : i.val < 1 := i.isLt
              have hi0 : i.val = 0 := by omega
              have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
              rw [hi]
              exact heq
            have hsub : (f.toFun (Subtype.mk z hzI)) = (f.toFun (Subtype.mk (fun _ => t₁) ht1I)) :=
              Subtype.ext hval
            have heqZX : z = (fun _ => t₁) := hinj z _ hzI ht1I hsub
            have hcon : Lt1 (fun _ => t₁) (fun _ => t₁) := heqZX ▸ hzx
            exact lt_irrefl _ hcon
          · exact False.elim (hne h)
        have hgoal : Lt1 w1 (f.toFun (Subtype.mk z hzI)).1 := by
          rw [eW1]
          exact lt_trans hfmX' hzt1
        exact hgoal
    -- m₁' lies in T₀ by partition; it is strictly below min T₀: contradiction.
    have hm₁'T₀ : T₀ (fun _ => m₁') := by
      rw [hTdef]
      have hmJ' : openInterval a b (fun _ => m₁') := by
        obtain ⟨s0, hs0⟩ := hSne₁
        have hs0' : openInterval a b s0 ∧ Lt1 s0 (fun _ => t₁) ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append s0 w) ∧
              Lt1 w v₁) := by
          rw [hS₁def] at hs0
          exact hs0
        obtain ⟨hs0J, hs0x, -⟩ := hs0'
        have hs0le : LT.lt (Power.coord1 s0) m₁' ∨ Power.coord1 s0 = m₁' :=
          hUBm' s0 hs0
        have haM : Endpoint.lt a (Endpoint.finite m₁') := by
          rcases hs0le with h | h
          · exact loTrans a hs0J.left h
          · rw [← h]
            exact hs0J.left
        have hMb : Endpoint.lt (Endpoint.finite m₁') b :=
          hiTrans b ht1J.right hmX'
        exact ⟨haM, hMb⟩
      have hxmM' : Lt1 (fun _ => m₁') x₀ := lt_trans hmX' ht1x
      refine ⟨hmJ', ?_, ?_, ?_⟩
      · exact hxmM'
      · -- f(m̂') < f(x₀) via f(t₁).
        have hft1x : Lt1 (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1
            (f.toFun (Subtype.mk x₀ hx₀I)).1 := by
          have ht1T' : openInterval a b (fun _ => t₁) ∧ Lt1 (fun _ => t₁) x₀ ∧
              (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                (A := I) (B := B) f.toFun (Power.append (fun _ => t₁) w) ∧
                Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
              (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
                Lt1 (fun _ => t₁) z → Lt1 z x₀ →
                (LT.lt (Power.coord1 (fun _ => t₁)) (Power.coord1 z) ∨
                  Power.coord1 (fun _ => t₁) = Power.coord1 z) →
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => t₁) w1) →
                Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) := ht1T
          obtain ⟨-, -, hPREt, -⟩ := ht1T'
          obtain ⟨w, hGw, hwlt⟩ := hPREt
          have eW : w = (f.toFun (Subtype.mk (fun _ : Fin 1 => t₁) ht1I)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append (fun _ : Fin 1 => t₁) w) = (fun _ : Fin 1 => t₁) :=
              appendLeftAux _ _
            have eR : Power.right (Power.append (fun _ : Fin 1 => t₁) w) = w :=
              appendRightAux _ _
            calc w = Power.right (Power.append (fun _ : Fin 1 => t₁) w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => t₁) w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => t₁) ht1I)).1 := by simp only [eL]
          rw [eW] at hwlt
          exact hwlt
        have eLm : Power.left (Power.append (fun _ : Fin 1 => m₁')
            ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) = (fun _ : Fin 1 => m₁') :=
          appendLeftAux _ _
        have eRm : Power.right (Power.append (fun _ : Fin 1 => m₁')
            ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) =
            (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 :=
          appendRightAux _ _
        have hGm : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append (fun _ : Fin 1 => m₁') ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) :=
          ⟨eLm.symm ▸ hmI', by simp only [eLm, eRm]⟩
        exact ⟨(f.toFun (Subtype.mk (fun _ => m₁') hmI')).1, hGm, lt_trans hfmX' hft1x⟩
      · intro z w1 hzI hzJ hyz hzx hle hGyw1
        have eW1 : w1 = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 := by
          obtain ⟨hx0, heq0⟩ := hGyw1
          have eL : Power.left (Power.append (fun _ : Fin 1 => m₁') w1) = (fun _ : Fin 1 => m₁') :=
            appendLeftAux _ _
          have eR : Power.right (Power.append (fun _ : Fin 1 => m₁') w1) = w1 :=
            appendRightAux _ _
          calc w1 = Power.right (Power.append (fun _ : Fin 1 => m₁') w1) := eR.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => m₁') w1)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 := by simp only [eL]
        have hgoal : Lt1 w1 (f.toFun (Subtype.mk z hzI)).1 := by
          rw [eW1]
          rcases lt_trichotomy (Power.coord1 z) t₁ with h | h | h
          · have hlt1 := h
            by_contra hne
            rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
                (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁') hmI')).1)) with h2 | h2 | h2
            · have hzS : S₁ z := by
                rw [hS₁def]
                have eLz : Power.left (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) = z :=
                  appendLeftAux _ _
                have eRz : Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) =
                    (f.toFun (Subtype.mk z hzI)).1 :=
                  appendRightAux _ _
                have hGz : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) :=
                  ⟨eLz.symm ▸ hzI, by simp only [eLz, eRz]⟩
                have hltz : Lt1 ((f.toFun (Subtype.mk z hzI)).1)
                    (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := by
                  have h1 : LT.lt (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
                      (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁') hmI')).1)) := h2
                  have h2x : Lt1 (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1
                      (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := hfmX'
                  exact lt_trans h1 h2x
                have hzt1 : Lt1 z (fun _ => t₁) := hlt1
                exact ⟨hzJ, hzt1, _, hGz, hltz⟩
              have hzUB : LT.lt (Power.coord1 z) m₁' ∨ Power.coord1 z = m₁' :=
                hUBm' z hzS
              have hzm : Lt1 (fun _ => m₁') z := hyz
              rcases hzUB with h3 | h3
              · exact lt_irrefl _ (lt_trans hzm h3)
              · have hzm' : LT.lt m₁' (Power.coord1 z) := hzm
                rw [h3] at hzm'
                exact lt_irrefl _ hzm'
            · have heq := h2
              exfalso
              have hval : (f.toFun (Subtype.mk z hzI)).1 =
                  (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 := by
                funext i
                have hiv : i.val < 1 := i.isLt
                have hi0 : i.val = 0 := by omega
                have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
                rw [hi]
                exact heq
              have hsub : (f.toFun (Subtype.mk z hzI)) =
                  (f.toFun (Subtype.mk (fun _ => m₁') hmI')) :=
                Subtype.ext hval
              have heqZM : z = (fun _ => m₁') := hinj z _ hzI hmI' hsub
              have hcon : Lt1 (fun _ => m₁') (fun _ => m₁') := heqZM ▸ hyz
              exact lt_irrefl _ hcon
            · exact False.elim (hne h2)
          · have heq := h
            have ept : z = (fun _ => t₁) := ptEqAux heq
            subst ept
            exact hfmX'
          · have hgt := h
            have htz : Lt1 (fun _ => t₁) z := hgt
            have ht1T' : openInterval a b (fun _ => t₁) ∧ Lt1 (fun _ => t₁) x₀ ∧
                (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                  (A := I) (B := B) f.toFun (Power.append (fun _ => t₁) w) ∧
                  Lt1 w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
                (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
                  Lt1 (fun _ => t₁) z → Lt1 z x₀ →
                  (LT.lt (Power.coord1 (fun _ => t₁)) (Power.coord1 z) ∨
                    Power.coord1 (fun _ => t₁) = Power.coord1 z) →
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => t₁) w1) →
                  Lt1 w1 (f.toFun (Subtype.mk z hzI)).1) := ht1T
            obtain ⟨-, -, -, ht1U⟩ := ht1T'
            have hleTZ : LT.lt (Power.coord1 (fun _ => t₁)) (Power.coord1 z) ∨
                Power.coord1 (fun _ => t₁) = Power.coord1 z := Or.inl hgt
            have eLt : Power.left (Power.append (fun _ : Fin 1 => t₁)
                ((f.toFun (Subtype.mk (fun _ : Fin 1 => t₁) ht1I)).1)) = (fun _ : Fin 1 => t₁) :=
              appendLeftAux _ _
            have eRt : Power.right (Power.append (fun _ : Fin 1 => t₁)
                ((f.toFun (Subtype.mk (fun _ : Fin 1 => t₁) ht1I)).1)) =
                (f.toFun (Subtype.mk (fun _ : Fin 1 => t₁) ht1I)).1 :=
              appendRightAux _ _
            have hGt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ => t₁) ((f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1)) :=
              ⟨eLt.symm ▸ ht1I, by simp only [eLt, eRt]⟩
            have htzv : Lt1 (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1
                (f.toFun (Subtype.mk z hzI)).1 :=
              ht1U z _ hzI hzJ htz hzx hleTZ hGt
            exact lt_trans hfmX' htzv
        exact hgoal
    -- Contradiction with minimality of t₁.
    have hmemM : Power.coord1 (fun _ => m₁') ∈ TF := hTFmp _ hm₁'T₀
    have hconLeast : LT.lt t₁ (Power.coord1 (fun _ => m₁')) ∨
        t₁ = Power.coord1 (fun _ => m₁') :=
      ht1Least (Power.coord1 (fun _ => m₁')) hmemM
    have hFalse : False := by
      have hltMT : LT.lt m₁' t₁ := hmX'
      rcases hconLeast with h | h
      · exact lt_irrefl _ (lt_trans hltMT h)
      · exact lt_irrefl _ (h ▸ hltMT)
    exact False.elim hFalse
  · -- Empty window: take (a,b) itself, vacuously increasing.
    refine ⟨a, b, hlt, hsubJ, ?_⟩
    intro x hxI y hyI hx hy hxy
    exact False.elim (hJne ⟨x, hx⟩)
