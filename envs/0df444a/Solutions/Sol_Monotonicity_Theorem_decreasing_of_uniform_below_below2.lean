-- Prove2me | solution 1 for Monotonicity_Theorem.decreasing_of_uniform_below_below2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T00:44:19.683985+00:00
-- url     : https://prove2.me/submissions/fa4be2e5-fdce-4ce8-92ba-e73460341e1d

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval2
import Mathlib.Data.Finset.Max

open Classical
open Monotonicity_Theorem

theorem Monotonicity_Theorem.incompatible_decreasing_below_below {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Endpoint R} (hsubJ : ∀ x, openInterval a b x → I x)
    (hU : ∀ x (hxI : I x), openInterval a b x ->
        ∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
        Lt1 c1 x ∧ Lt1 x c2 ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 c1 y → Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 x y → Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1))
    {u v : R} (huv : LT.lt u v)
    (hsub : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval a b x)
    (hdec : ∀ x (hxI : I x) y (hyI : I y),
      openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval (Endpoint.finite u) (Endpoint.finite v) y ->
      Lt1 x y → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) :
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
  have hdecZY : Lt1 (f.toFun (Subtype.mk (fun _ => r2) hyI)).1
      (f.toFun (Subtype.mk (fun _ => rr) hzI)).1 :=
    hdec _ hzI _ hyI hzJ hyJ hzy
  have hwin : Lt1 (f.toFun (Subtype.mk (fun _ => rr) hzI)).1
      (f.toFun (Subtype.mk (fun _ => r2) hyI)).1 := by
    have hzJab : openInterval a b (fun _ => rr) := hsub _ hzJ
    have hc1z : Lt1 c1 (fun _ => rr) := hrr2
    have hzyab : Lt1 (fun _ => rr) (fun _ => r2) := hrr3
    exact hleft _ hzI hzJab hc1z hzyab
  exact lt_irrefl _ (lt_trans hdecZY hwin)


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

theorem ptEqAux {R : Type} {p q : Power R 1}
    (h : Power.coord1 p = Power.coord1 q) : p = q := by
  funext i
  have hiv : i.val < 1 := i.isLt
  have hi0 : i.val = 0 := by omega
  have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
  rw [hi]
  exact h

-- Inlined order-bound infrastructure (verbatim BoundsBelow).
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

-- Above-infimum points exist (from greatest-lower-bound property).
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

-- Inlined infimum tower (verbatim copies, renamed).
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

-- Index maps into arity 1 + (1 + (1 + 1)) for right-maxima.
-- Positions (flattened): x = 0, y = 1, w = 2, v = 3.
def rMX : Fin 1 → Fin (1 + (1 + (1 + 1))) :=
  fun _ => ⟨0, by decide⟩

def rMY : Fin 1 → Fin (1 + (1 + (1 + 1))) :=
  fun _ => ⟨1, by decide⟩

def rMLT : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

def rMGW : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩

def rMGX : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩

def rMBAD : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨3, by decide⟩ else ⟨2, by decide⟩

def preW : Fin 1 → Fin (1 + 1) := fun _ => ⟨1, by decide⟩

end Monotonicity_Theorem

open Monotonicity_Theorem

-- Right-global maxima on a window form a definable set.
theorem rightMaxDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R) :
    M.S 1 (fun x : Power R 1 => openInterval a b x ∧
      ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 x y ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) ->
        Lt1 w v) := by
  have hJmem : M.S 1 (openInterval a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hF : M.S (1 + (1 + (1 + 1)))
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (rMX i)) ∧
        I (fun i : Fin 1 => q (rMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (rMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (rMLT j)) 0)
          ((fun j : Fin 2 => q (rMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (rMBAD j)) 0)
          ((fun j : Fin 2 => q (rMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem rMX hJmem)
      (M.inter_mem (M.reindex_mem rMY f.domain_mem)
        (M.inter_mem (M.reindex_mem rMY hJmem)
          (M.inter_mem (M.reindex_mem rMLT M.lt_mem)
            (M.inter_mem (M.reindex_mem rMGW f.graph_mem)
              (M.inter_mem (M.reindex_mem rMGX f.graph_mem)
                (M.union_mem (M.reindex_mem rMBAD M.lt_mem)
                  (M.diagonal_mem (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
                    (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) (by decide))))))))
  have hProj : M.S 1 (fun x : Power R 1 => ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (rMX i)) ∧
        I (fun i : Fin 1 => q (rMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (rMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (rMLT j)) 0)
          ((fun j : Fin 2 => q (rMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (rMBAD j)) 0)
          ((fun j : Fin 2 => q (rMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)) :=
    M.existsLast_mem hF
  have hC : M.S 1 (fun x : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (rMX i)) ∧
        I (fun i : Fin 1 => q (rMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (rMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (rMLT j)) 0)
          ((fun j : Fin 2 => q (rMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (rMBAD j)) 0)
          ((fun j : Fin 2 => q (rMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)) :=
    M.compl_mem hProj
  have hJX : M.S 1 ((openInterval a b) ∩
      (fun x : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (rMX i)) ∧
        I (fun i : Fin 1 => q (rMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (rMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (rMLT j)) 0)
          ((fun j : Fin 2 => q (rMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (rMBAD j)) 0)
          ((fun j : Fin 2 => q (rMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t))) :=
    M.inter_mem hJmem hC
  have heqR : ((openInterval a b) ∩
      (fun x : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval a b (fun i : Fin 1 => q (rMX i)) ∧
        I (fun i : Fin 1 => q (rMY i)) ∧
        openInterval a b (fun i : Fin 1 => q (rMY i)) ∧
        LT.lt ((fun j : Fin 2 => q (rMLT j)) 0)
          ((fun j : Fin 2 => q (rMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (rMGX j)) ∧
        (LT.lt ((fun j : Fin 2 => q (rMBAD j)) 0)
          ((fun j : Fin 2 => q (rMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)))
      = (fun x : Power R 1 => openInterval a b x ∧
        ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 x y ->
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w) ->
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x v) ->
          Lt1 w v) := by
    funext x
    apply propext
    constructor
    · intro h
      obtain ⟨hJx, hn⟩ := h
      refine ⟨hJx, ?_⟩
      intro y w v hy hyJ hxy hGyw hGxv
      have eY : (fun i : Fin 1 => (Power.append x
              (Power.append y (Power.append w v))) (rMY i)) = y := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      have gXY : LT.lt ((fun j : Fin 2 => (Power.append x
              (Power.append y (Power.append w v))) (rMLT j)) 0)
          ((fun j : Fin 2 => (Power.append x
              (Power.append y (Power.append w v))) (rMLT j)) 1) := hxy
      have eGW : (fun j : Fin (1 + 1) => (Power.append x
              (Power.append y (Power.append w v))) (rMGW j))
          = Power.append y w := by
        funext j
        by_cases hj : j.val = 0
        · have e : rMGW j
              = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGW, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x
                (Power.append y (Power.append w v))) (rMGW j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj0]
        · have e : rMGW j
              = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGW, hj]
          have jv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append x
                (Power.append y (Power.append w v))) (rMGW j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = w ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => (Power.append x
              (Power.append y (Power.append w v))) (rMGX j))
          = Power.append x v := by
        funext j
        by_cases hj : j.val = 0
        · have e : rMGX j
              = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGX, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x
                (Power.append y (Power.append w v))) (rMGX j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x v)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x v (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x v) j := by rw [hj0]
        · have e : rMGX j
              = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGX, hj]
          have jv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append x
                (Power.append y (Power.append w v))) (rMGX j)
              = (Power.append x
                (Power.append y (Power.append w v)))
                (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = v ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x v)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right x v (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x v) j := by rw [hj1]
      have hIY : I (fun i : Fin 1 => (Power.append x
          (Power.append y (Power.append w v))) (rMY i)) := by
        rw [eY]
        exact hy
      have hJY : openInterval a b (fun i : Fin 1 => (Power.append x
          (Power.append y (Power.append w v))) (rMY i)) := by
        rw [eY]
        exact hyJ
      have hGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => (Power.append x
            (Power.append y (Power.append w v))) (rMGW j)) := by
        rw [eGW]
        exact hGyw
      have hGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => (Power.append x
            (Power.append y (Power.append w v))) (rMGX j)) := by
        rw [eGX]
        exact hGxv
      cases lt_trichotomy (Power.coord1 w) (Power.coord1 v) with
      | inl hTri =>
        exact hTri
      | inr h =>
        cases h with
        | inl h =>
          have gEq : (Power.append x (Power.append y (Power.append w v)))
                (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
              = (Power.append x (Power.append y (Power.append w v)))
                (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := h
          exact False.elim (hn ⟨Power.append y (Power.append w v),
            hJx, hIY, hJY, gXY, hGW, hGX, Or.inr gEq⟩)
        | inr h =>
          have gLt : LT.lt ((fun j : Fin 2 => (Power.append x
                  (Power.append y (Power.append w v))) (rMBAD j)) 0)
              ((fun j : Fin 2 => (Power.append x
                  (Power.append y (Power.append w v))) (rMBAD j)) 1) := h
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
      have eY' : (fun i : Fin 1 => (Power.append x t) (rMY i)) = y := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      have eGWt : (fun j : Fin (1 + 1) => (Power.append x t) (rMGW j))
          = Power.append y w := by
        funext j
        by_cases hj : j.val = 0
        · have e : rMGW j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGW, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x t) (rMGW j)
              = (Power.append x t) (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj0]
        · have e : rMGW j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGW, hj]
          have hjv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
          calc (Power.append x t) (rMGW j)
              = (Power.append x t) (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = w ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y w)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y w (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y w) j := by rw [hj1]
      have eGXt : (fun j : Fin (1 + 1) => (Power.append x t) (rMGX j))
          = Power.append x v := by
        funext j
        by_cases hj : j.val = 0
        · have e : rMGX j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGX, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append x t) (rMGX j)
              = (Power.append x t) (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x v)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x v (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x v) j := by rw [hj0]
        · have e : rMGX j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
            simp [rMGX, hj]
          have hjv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
          calc (Power.append x t) (rMGX j)
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
      have hxy : Lt1 x y := hLT
      have hGyw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) := by
        rw [← eGWt]
        exact hGW
      have hGxv : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) := by
        rw [← eGXt]
        exact hGX
      have hval : Lt1 w v := hall y w v hy hyJ hxy hGyw hGxv
      rcases hBad with hBADlt | hBADeq
      · have hLT2' : LT.lt (Power.coord1 v) (Power.coord1 w) := hBADlt
        have hval' : LT.lt (Power.coord1 w) (Power.coord1 v) := hval
        exact lt_irrefl _ (lt_trans hval' hLT2')
      · have heq' : Power.coord1 w = Power.coord1 v := hBADeq
        have hval' : LT.lt (Power.coord1 w) (Power.coord1 v) := hval
        rw [heq'] at hval'
        exact lt_irrefl _ hval'
  rw [← heqR]
  exact hJX

-- Values below a fixed bound attained to the right: preimage is definable.
theorem abovePreimageDefinable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R)
    (x₀ : Power R 1) (hx₀I : I x₀) :
    M.S 1 (fun y : Power R 1 => openInterval a b y ∧
      Lt1 x₀ y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w)) := by
  have hJmem : M.S 1 (openInterval a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hXGT : M.S 1 (openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hW : M.S 1 (openInterval
      (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1))) Endpoint.posInf) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hG2 : M.S (1 + 1)
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1))) Endpoint.posInf
          (fun i : Fin 1 => q (preW i))) :=
    M.inter_mem f.graph_mem (M.reindex_mem preW hW)
  have hPRE : M.S 1 (fun y : Power R 1 => ∃ w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1))) Endpoint.posInf
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w)) :=
    M.existsLast_mem hG2
  have hS : M.S 1 (((openInterval a b) ∩
      (openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf)) ∩
      (fun y : Power R 1 => ∃ w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1))) Endpoint.posInf
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w))) :=
    M.inter_mem (M.inter_mem hJmem hXGT) hPRE
  have heqS : (((openInterval a b) ∩
      (openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf)) ∩
      (fun y : Power R 1 => ∃ w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1))) Endpoint.posInf
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w)))
      = (fun y : Power R 1 => openInterval a b y ∧
        Lt1 x₀ y ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w)) := by
    funext y
    apply propext
    constructor
    · intro h
      obtain ⟨hJX, hRest⟩ := h
      obtain ⟨hJy, hXy⟩ := hJX
      obtain ⟨w, hG, hWlt⟩ := hRest
      have hxy : Lt1 x₀ y := by
        obtain ⟨hlt1, -⟩ := hXy
        exact hlt1
      have hwlt : Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w := by
        obtain ⟨hlt1, -⟩ := hWlt
        exact hlt1
      exact ⟨hJy, hxy, ⟨w, hG, hwlt⟩⟩
    · intro h
      obtain ⟨hJy, hxy, hPREw⟩ := h
      obtain ⟨w, hG, hwlt⟩ := hPREw
      have hXy : openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf y :=
        ⟨hxy, trivial⟩
      have hWlt : openInterval
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1))) Endpoint.posInf w :=
        ⟨hwlt, trivial⟩
      exact ⟨⟨hJy, hXy⟩, ⟨w, hG, hWlt⟩⟩
  rw [← heqS]
  exact hS

namespace Monotonicity_Theorem

-- Index maps into arity 1 + (1 + (1 + 1)) for right-candidates.
-- Positions (flattened): y = 0, z = 1, w1 = 2, w2 = 3.
def tDZ : Fin 1 → Fin (1 + (1 + (1 + 1))) :=
  fun _ => ⟨1, by decide⟩

def tDLT : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

def tDG1 : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩

def tDG2 : Fin (1 + 1) → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨3, by decide⟩

def tDBAD : Fin 2 → Fin (1 + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨2, by decide⟩ else ⟨3, by decide⟩

end Monotonicity_Theorem

open Monotonicity_Theorem

-- Candidate sets (right-to-x0 minima below x0's value) are definable.
theorem candDefinableR {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R)
    (x₀ : Power R 1) (hx₀I : I x₀) :
    M.S 1 (fun y : Power R 1 => openInterval a b y ∧ Lt1 x₀ y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w) ∧
      (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
        Lt1 x₀ z → Lt1 z y →
        (LT.lt (Power.coord1 z) (Power.coord1 y) ∨ Power.coord1 z = Power.coord1 y) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 (f.toFun (Subtype.mk z hzI)).1 w1)) := by
  have hJmem : M.S 1 (openInterval a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hXz : M.S 1 (openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hPREfull : M.S 1 (fun y : Power R 1 => openInterval a b y ∧
      Lt1 x₀ y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w)) :=
    abovePreimageDefinable M f a b x₀ hx₀I
  have hF : M.S (1 + (1 + (1 + 1)))
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf
          (fun i : Fin 1 => q (tDZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tDBAD j)) 0)
          ((fun j : Fin 2 => q (tDBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem tDZ f.domain_mem)
      (M.inter_mem (M.reindex_mem tDZ hJmem)
        (M.inter_mem (M.reindex_mem tDZ hXz)
          (M.inter_mem (M.reindex_mem tDLT M.lt_mem)
            (M.inter_mem
              (M.union_mem (M.reindex_mem tDLT M.lt_mem)
                (M.diagonal_mem (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
                  (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) (by decide)))
              (M.inter_mem (M.reindex_mem tDG1 f.graph_mem)
                (M.inter_mem (M.reindex_mem tDG2 f.graph_mem)
                  (M.union_mem (M.reindex_mem tDBAD M.lt_mem)
                    (M.diagonal_mem (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
                      (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) (by decide)))))))))
  have hProj : M.S 1 (fun y : Power R 1 => ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf
          (fun i : Fin 1 => q (tDZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tDBAD j)) 0)
          ((fun j : Fin 2 => q (tDBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 1 (fun y : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf
          (fun i : Fin 1 => q (tDZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tDBAD j)) 0)
          ((fun j : Fin 2 => q (tDBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)) :=
    M.compl_mem hProj
  have hPREfull : M.S 1 (fun y : Power R 1 => openInterval a b y ∧
      Lt1 x₀ y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w)) :=
    abovePreimageDefinable M f a b x₀ hx₀I
  have hTmem : M.S 1 (setInter
      (fun y : Power R 1 => openInterval a b y ∧
        Lt1 x₀ y ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w))
      (fun y : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf
          (fun i : Fin 1 => q (tDZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tDBAD j)) 0)
          ((fun j : Fin 2 => q (tDBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t))) :=
    M.inter_mem hPREfull hC
  have heqT : (setInter
      (fun y : Power R 1 => openInterval a b y ∧
        Lt1 x₀ y ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w))
      (fun y : Power R 1 => ¬ ∃ t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval a b (fun i : Fin 1 => q (tDZ i)) ∧
        openInterval (Endpoint.finite (Power.coord1 x₀)) Endpoint.posInf
          (fun i : Fin 1 => q (tDZ i)) ∧
        LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∧
        (LT.lt ((fun j : Fin 2 => q (tDLT j)) 0)
          ((fun j : Fin 2 => q (tDLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tDG2 j)) ∧
        (LT.lt ((fun j : Fin 2 => q (tDBAD j)) 0)
          ((fun j : Fin 2 => q (tDBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)))
      = (fun y : Power R 1 => openInterval a b y ∧ Lt1 x₀ y ∧
        (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 (f.toFun (Subtype.mk x₀ hx₀I)).1 w) ∧
        (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
          Lt1 x₀ z → Lt1 z y →
          (LT.lt (Power.coord1 z) (Power.coord1 y) ∨ Power.coord1 z = Power.coord1 y) →
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w1) →
          Lt1 (f.toFun (Subtype.mk z hzI)).1 w1)) := by
    funext y
    apply propext
    constructor
    · intro h
      obtain ⟨hPRE, hn⟩ := h
      obtain ⟨hJy, hXy, hPREw⟩ := hPRE
      obtain ⟨wY, hGY, hWlt⟩ := hPREw
      have hltYX : Lt1 x₀ y := hXy
      refine ⟨hJy, hltYX, ⟨wY, hGY, hWlt⟩, ?_⟩
      intro z w1 hzI hzJ hxz hzy hle hGyw1
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
      rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
          (Power.coord1 w1) with
        hTri | heqC | hgtC
      · have hv : Lt1 ((f.toFun (Subtype.mk z hzI)).1) w1 := hTri
        exact hv
      · have heqV := heqC
        exfalso
        apply hn
        use Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1))
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzI
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzJ
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact ⟨hxz, trivial⟩
        · exact hzy
        · cases hle with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h.symm
        · have eT1t : (fun j : Fin (1 + 1) => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDG1 j))
              = Power.append y w1 := by
            funext j
            by_cases hj : j.val = 0
            · have e : tDG1 j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG1, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG1 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append y w1)
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left y w1 (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append y w1) j := by rw [hj0]
            · have e : tDG1 j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG1, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG1 j)
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
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDG2 j))
              = Power.append z ((f.toFun (Subtype.mk z hzI)).1) := by
            funext j
            by_cases hj : j.val = 0
            · have e : tDG2 j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG2, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG2 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left z _ (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj0]
            · have e : tDG2 j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG2, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG2 j)
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
        · exact Or.inr heqV.symm
      · have hgt := hgtC
        exfalso
        apply hn
        use Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1))
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzI
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact hzJ
        · have eZt : (fun i : Fin 1 => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDZ i)) = z := by
            funext i
            have hiv : i.val < 1 := i.isLt
            have hi0 : i.val = 0 := by omega
            have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
            rw [hi]
            rfl
          rw [eZt]
          exact ⟨hxz, trivial⟩
        · exact hzy
        · cases hle with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h.symm
        · have eT1t : (fun j : Fin (1 + 1) => (Power.append y
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDG1 j))
              = Power.append y w1 := by
            funext j
            by_cases hj : j.val = 0
            · have e : tDG1 j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG1, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG1 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append y w1)
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left y w1 (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append y w1) j := by rw [hj0]
            · have e : tDG1 j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG1, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG1 j)
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
              (Power.append z (Power.append w1 ((f.toFun (Subtype.mk z hzI)).1)))) (tDG2 j))
              = Power.append z ((f.toFun (Subtype.mk z hzI)).1) := by
            funext j
            by_cases hj : j.val = 0
            · have e : tDG2 j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG2, hj]
              have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG2 j)
                  = (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1))))
                    (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
                _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                    (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                    (Fin.append_left z _ (⟨0, by decide⟩ : Fin 1)).symm
                _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj0]
            · have e : tDG2 j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
                simp [tDG2, hj]
              have hjv : j.val = 1 := by omega
              have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
              calc (Power.append y (Power.append z (Power.append w1
                    ((f.toFun (Subtype.mk z hzI)).1)))) (tDG2 j)
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
        have eZt : (fun i : Fin 1 => (Power.append y t) (tDZ i)) = z := by
          funext i
          have hiv : i.val < 1 := i.isLt
          have hi0 : i.val = 0 := by omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          rfl
        have eT1t : (fun j : Fin (1 + 1) => (Power.append y t) (tDG1 j))
            = Power.append y w1 := by
          funext j
          by_cases hj : j.val = 0
          · have e : tDG1 j = (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tDG1, hj]
            have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
            calc (Power.append y t) (tDG1 j)
                = (Power.append y t) (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
              _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append y w1)
                  (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_left y w1 (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append y w1) j := by rw [hj0]
          · have e : tDG1 j = (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tDG1, hj]
            have hjv : j.val = 1 := by omega
            have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
            calc (Power.append y t) (tDG1 j)
                = (Power.append y t) (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
              _ = w1 ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append y w1)
                  (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_right y w1 (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append y w1) j := by rw [hj1]
        have eT2t : (fun j : Fin (1 + 1) => (Power.append y t) (tDG2 j))
            = Power.append z w2 := by
          funext j
          by_cases hj : j.val = 0
          · have e : tDG2 j = (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tDG2, hj]
            have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
            calc (Power.append y t) (tDG2 j)
                = (Power.append y t) (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by rw [e]
              _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append z w2)
                  (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_left z w2 (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append z w2) j := by rw [hj0]
          · have e : tDG2 j = (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := by
              simp [tDG2, hj]
            have hjv : j.val = 1 := by omega
            have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
            calc (Power.append y t) (tDG2 j)
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
        have hxz : Lt1 x₀ z := by
          rw [eZt] at hXz
          obtain ⟨hlt1, -⟩ := hXz
          exact hlt1
        have hzy : Lt1 z y := hLT
        have hleZY : LT.lt (Power.coord1 z) (Power.coord1 y) ∨
            Power.coord1 z = Power.coord1 y := by
          rcases hLE with hLT2 | hEQ
          · exact Or.inl hLT2
          · exact Or.inr hEQ.symm
        have hGyw1 : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w1) := by
          rw [← eT1t]
          exact hG1
        have hGzw2 : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append z w2) := by
          rw [← eT2t]
          exact hG2
        have hval : Lt1 (f.toFun (Subtype.mk z hzI)).1 w1 :=
          hall z w1 hzI hzJ hxz hzy hleZY hGyw1
        have eW : w2 = (f.toFun (Subtype.mk z hzI)).1 := by
          obtain ⟨hx0, heq0⟩ := hGzw2
          have eL0 : Power.left (Power.append z w2) = z := appendLeftAux _ _
          have eR0 : Power.right (Power.append z w2) = w2 := appendRightAux _ _
          calc w2 = Power.right (Power.append z w2) := eR0.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append z w2)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk z hzI)).1 := by simp only [eL0]
        rcases hBAD with hBADlt | hBADeq
        · have hLT2' : LT.lt (Power.coord1 w1) (Power.coord1 w2) := hBADlt
          have hval' : LT.lt (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
              (Power.coord1 w1) := hval
          rw [eW] at hLT2'
          exact lt_irrefl _ (lt_trans hval' hLT2')
        · have heq' : Power.coord1 w1 = Power.coord1 w2 := hBADeq
          have hval' : LT.lt (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
              (Power.coord1 w1) := hval
          rw [eW] at heq'
          rw [heq'] at hval'
          exact lt_irrefl _ hval'
  rw [← heqT]
  exact hTmem

-- Difficult below_below case: uniform peaks are impossible for injective f.
-- Derive False via right-global maxima, candidate infima, and nested maxima.
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
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 x y → Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) :
    ∃ a2 b2 : Endpoint R, Endpoint.lt a2 b2 ∧
      (∀ x, openInterval a2 b2 x → I x) ∧
      (∀ x (hxI : I x) y (hyI : I y), openInterval a2 b2 x → openInterval a2 b2 y ->
        Lt1 x y → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) := by
  by_cases hJne : (openInterval a b).Nonempty
  · -- Nonempty window: derive False.
    set L : Set (Power R 1) := fun x : Power R 1 => openInterval a b x ∧
      ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 x y ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) ->
        Lt1 w v with hLdef
    have hLmem : M.S 1 L := rightMaxDefinable M f a b
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
        have hxL : L x := hsubAB (hsubUV x hjx)
        have hxL' : openInterval a b x ∧
            (∀ y0 w v : Power R 1, I y0 → openInterval a b y0 → Lt1 x y0 ->
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append y0 w) ->
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x v) ->
              Lt1 w v) := hxL
        have hallX : ∀ y0 w v : Power R 1, I y0 → openInterval a b y0 → Lt1 x y0 ->
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y0 w) ->
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append x v) ->
            Lt1 w v := hxL'.right
        have hyJab : openInterval a b y := hsub _ hjy
        have hyI' : I y := hsubJ _ hyJab
        have eLy : Power.left (Power.append y ((f.toFun (Subtype.mk y hyI')).1)) = y :=
          appendLeftAux _ _
        have eRy : Power.right (Power.append y ((f.toFun (Subtype.mk y hyI')).1)) =
            (f.toFun (Subtype.mk y hyI')).1 :=
          appendRightAux _ _
        have hGy : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y ((f.toFun (Subtype.mk y hyI')).1)) :=
          ⟨eLy.symm ▸ hyI', by simp only [eLy, eRy]⟩
        have eLx : Power.left (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) = x :=
          appendLeftAux _ _
        have eRx : Power.right (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) =
            (f.toFun (Subtype.mk x hxI)).1 :=
          appendRightAux _ _
        have hGx : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) :=
          ⟨eLx.symm ▸ hxI, by simp only [eLx, eRx]⟩
        exact hallX y _ _ hyI' hyJab hxy hGy hGx
      exact Monotonicity_Theorem.incompatible_decreasing_below_below M f
        hsubJ hU huv hsub hdec
    -- Base left endpoint: max of L, or a if L is empty.
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
    have ha' : ∃ bp : Endpoint R, Endpoint.lt bp b ∧
        (∀ x, openInterval bp b x → x ∉ L) ∧
        (∀ x, openInterval bp b x → openInterval a b x) := by
      by_cases hLFempty : LF = ∅
      · refine ⟨a, hlt, ?_, ?_⟩
        · intro x hx hxL
          have hmem : Power.coord1 x ∈ LF := hLFmp x hxL
          rw [hLFempty] at hmem
          exact Finset.notMem_empty _ hmem
        · intro x hx
          exact hx
      · have hLFne : LF.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLFempty
        obtain ⟨m, hmMem, hmLe⟩ : ∃ m, m ∈ LF ∧ ∀ r ∈ LF, r ≤ m :=
          ⟨LF.max' hLFne, Finset.max'_mem LF hLFne, fun r hr => Finset.le_max' LF r hr⟩
        have hmGreat : ∀ r ∈ LF, LT.lt r m ∨ r = m :=
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
        refine ⟨Endpoint.finite m, hmb', ?_, ?_⟩
        · intro x hx hxL
          have hmem : Power.coord1 x ∈ LF := hLFmp x hxL
          have hle := hmGreat (Power.coord1 x) hmem
          have hltxm : LT.lt m (Power.coord1 x) := hx.left
          rcases hle with h | h
          · exact lt_irrefl _ (lt_trans h hltxm)
          · rw [h] at hltxm
            exact lt_irrefl _ hltxm
        · intro x hx
          obtain ⟨hxlo, hxhi⟩ := hx
          refine ⟨?_, hxhi⟩
          exact loTrans a ham' hxlo
    obtain ⟨bp, hbpLt, hbpNoL, hbpSub⟩ := ha'
    -- Witness x₀ in (bp, b).
    have hAne : (openInterval bp b).Nonempty := by
      cases bp with
      | negInf =>
          cases b with
          | negInf => exact False.elim hbpLt
          | finite val =>
            obtain ⟨y, hym⟩ := exists_lt val
            exact ⟨fun _ => y, trivial, hym⟩
          | posInf =>
            obtain ⟨xJ, hxJ⟩ := hJne
            obtain ⟨-, hxhi⟩ := hxJ
            exact ⟨xJ, trivial, hxhi⟩
      | finite val =>
        cases b with
        | negInf => exact False.elim hbpLt
        | finite val2 =>
          have hlt2 : LT.lt val val2 := hbpLt
          obtain ⟨y, hy1, hy2⟩ := exists_between hlt2
          exact ⟨fun _ => y, hy1, hy2⟩
        | posInf =>
          obtain ⟨y, hym⟩ := exists_gt val
          exact ⟨fun _ => y, hym, trivial⟩
      | posInf =>
        cases b with
        | negInf => exact False.elim hbpLt
        | finite _ => exact False.elim hbpLt
        | posInf => exact False.elim hbpLt
    obtain ⟨x₀, hx₀mem⟩ := hAne
    have hx₀J : openInterval a b x₀ := hbpSub _ hx₀mem
    have hx₀nL : x₀ ∉ L := hbpNoL _ hx₀mem
    have hx₀I : I x₀ := hsubJ _ hx₀J
    set v₀ : Power R 1 := (f.toFun (Subtype.mk x₀ hx₀I)).1 with hv₀def
    set S : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧
      Lt1 x₀ y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 v₀ w) with hSdef
    -- S(x₀) is nonempty: x₀ is not a right-global maximum.
    have hNotAll : ¬ ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 x₀ y ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x₀ v) ->
        Lt1 w v := by
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
    have hyx : Lt1 x₀ y :=
      Classical.byContradiction (fun nb => hv1 (fun _ _ b _ _ => absurd b nb))
    have hGyw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y w) :=
      Classical.byContradiction (fun nc => hv1 (fun _ _ _ c _ => absurd c nc))
    have hGxv : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append x₀ v) :=
      Classical.byContradiction (fun nd => hv1 (fun _ _ _ _ d => absurd d nd))
    have hne : ¬ Lt1 w v :=
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
    have hltYX : Lt1 v₀ (f.toFun (Subtype.mk y hyI)).1 := by
      have hne' : ¬ Lt1 (f.toFun (Subtype.mk y hyI)).1 v₀ := by
        rw [hv₀def, ← eV, ← eW]
        exact hne
      rcases lt_trichotomy (Power.coord1 v₀)
          (Power.coord1 ((f.toFun (Subtype.mk y hyI)).1)) with h | h | h
      · exact h
      · have heq := h
        exfalso
        have hval : (f.toFun (Subtype.mk y hyI)).1 = v₀ := by
          funext i
          have hiv : i.val < 1 := i.isLt
          have hi0 : i.val = 0 := by omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          exact heq.symm
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
    have hSmem : M.S 1 S := abovePreimageDefinable M f a b x₀ hx₀I
    have hSne : S.Nonempty := ⟨y, hSwit⟩
    have hBnd : BoundedBelow1 S := by
      refine ⟨Power.coord1 x₀, ?_⟩
      intro s hs
      rw [hSdef] at hs
      obtain ⟨-, hlt, -⟩ := hs
      exact Or.inl hlt
    have hInf := infCompletenessAux S ((M.ominimal _).mp hSmem) hSne hBnd
    obtain ⟨m₁, hLBm, hGreatestm⟩ := hInf
    -- m₁ is strictly right of x₀ (S avoids the right window).
    obtain ⟨c1x, c2x, hc1Jx, hc2Jx, hc1x, hxx2, hleftx, hrightx⟩ :=
      hU x₀ hx₀I hx₀J
    have hxc2x : LT.lt (Power.coord1 x₀) (Power.coord1 c2x) := hxx2
    have hc2LB : IsLowerBound1 S (Power.coord1 c2x) := by
      intro s hs
      rw [hSdef] at hs
      obtain ⟨hsJ, hsx, hsW⟩ := hs
      obtain ⟨w, hGw, hwlt⟩ := hsW
      rcases lt_trichotomy (Power.coord1 s) (Power.coord1 c2x) with h | h | h
      · have hlt1 := h
        exfalso
        have hsJab : openInterval a b s := hsJ
        have hsI : I s := hsubJ _ hsJab
        have hxxs : Lt1 x₀ s := hsx
        have hsc2 : Lt1 s c2x := hlt1
        have hwin : Lt1 (f.toFun (Subtype.mk s hsI)).1 v₀ :=
          hrightx s hsI hsJab hxxs hsc2
        have hval : Lt1 v₀ (f.toFun (Subtype.mk s hsI)).1 := by
          have eW : w = (f.toFun (Subtype.mk s hsI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append s w) = s := appendLeftAux _ _
            have eR : Power.right (Power.append s w) = w := appendRightAux _ _
            calc w = Power.right (Power.append s w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append s w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk s hsI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hval hwin)
      · have heq := h
        exact Or.inr heq
      · have hlt2 := h
        exact Or.inl hlt2
    have hmLBc2 : LT.lt (Power.coord1 c2x) m₁ ∨ Power.coord1 c2x = m₁ :=
      hGreatestm _ hc2LB
    have hmX : LT.lt (Power.coord1 x₀) m₁ := by
      rcases hmLBc2 with h | h
      · exact lt_trans hxc2x h
      · rw [← h]
        exact hxc2x
    have hmJ : openInterval a b (fun _ => m₁) := by
      obtain ⟨s0, hs0⟩ := hSne
      have hs0' : openInterval a b s0 ∧ Lt1 x₀ s0 ∧
          (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
            (A := I) (B := B) f.toFun (Power.append s0 w) ∧
            Lt1 v₀ w) := by
        rw [hSdef] at hs0
        exact hs0
      obtain ⟨hs0J, hs0x, -⟩ := hs0'
      have hs0le : LT.lt m₁ (Power.coord1 s0) ∨ Power.coord1 s0 = m₁ :=
        hLBm s0 hs0
      have haM : Endpoint.lt a (Endpoint.finite m₁) :=
        loTrans a hx₀J.left hmX
      have hMb : Endpoint.lt (Endpoint.finite m₁) b := by
        rcases hs0le with h | h
        · exact hiTrans b hs0J.right h
        · rw [← h]
          exact hs0J.right
      exact ⟨haM, hMb⟩
    have hmI : I (fun _ => m₁) := hsubJ _ hmJ
    obtain ⟨c1m, c2m, hc1Jm, hc2Jm, hc1m, hxm2, hleftm, hrightm⟩ :=
      hU (fun _ => m₁) hmI hmJ
    -- f(x₀) < f(m₁): else the right window at m₁ contradicts minimality.
    have hfmX : Lt1 v₀ (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 := by
      by_contra hne
      have hgt : Lt1 (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 v₀ := by
        rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁) hmI)).1))
            (Power.coord1 v₀) with h | h | h
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
            exact heq
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
      have hmc2 : LT.lt m₁ (Power.coord1 c2m) := hxm2
      obtain ⟨sp, hspA, hsppt⟩ := notLBofGreatest S m₁ hGreatestm (Power.coord1 c2m) hmc2
      -- sp ∈ S below c2m; m₁ ≤ sp; case split
      have hsppm : LT.lt m₁ (Power.coord1 sp) ∨ Power.coord1 sp = m₁ :=
        hLBm sp hspA
      have hspJ : openInterval a b sp := by
        have hspA' : openInterval a b sp ∧ Lt1 x₀ sp ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append sp w) ∧
              Lt1 v₀ w) := hspA
        exact hspA'.left
      have hspI : I sp := hsubJ _ hspJ
      have hleSP : LT.lt (Power.coord1 sp) (Power.coord1 c2m) := hsppt
      rcases hsppm with h | h
      · -- m₁ < sp: right window gives f(sp) < f(m̂), but sp ∈ S gives f(x₀) < f(sp) < ... contra hgt.
        have hmsp : Lt1 (fun _ => m₁) sp := h
        have hspc2 : Lt1 sp c2m := hleSP
        have hfmsp : Lt1 (f.toFun (Subtype.mk sp hspI)).1
            (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 :=
          hrightm sp hspI hspJ hmsp hspc2
        have hspS : openInterval a b sp ∧ Lt1 x₀ sp ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append sp w) ∧
              Lt1 v₀ w) := hspA
        obtain ⟨-, hspx, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have hspx0 : Lt1 x₀ sp := hspx
        have hfx : Lt1 v₀ (f.toFun (Subtype.mk sp hspI)).1 := by
          have eW : w = (f.toFun (Subtype.mk sp hspI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append sp w) = sp := appendLeftAux _ _
            have eR : Power.right (Power.append sp w) = w := appendRightAux _ _
            calc w = Power.right (Power.append sp w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append sp w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk sp hspI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hfx (lt_trans hfmsp hgt))
      · -- sp = m₁ (coords): then sp ∈ S gives f(x₀) < f(m̂), contra hgt.
        have ept : sp = (fun _ => m₁) := ptEqAux h
        subst ept
        have hspS : openInterval a b (fun _ => m₁) ∧ Lt1 x₀ (fun _ => m₁) ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append (fun _ => m₁) w) ∧
              Lt1 v₀ w) := hspA
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
        exact lt_irrefl _ (lt_trans hwlt hgt)
    -- m₁ is a candidate for x₀.
    set T₀ : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧ Lt1 x₀ y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 v₀ w) ∧
      (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
        Lt1 x₀ z → Lt1 z y →
        (LT.lt (Power.coord1 z) (Power.coord1 y) ∨ Power.coord1 z = Power.coord1 y) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) with hTdef
    have hTmem : M.S 1 T₀ := candDefinableR M f a b x₀ hx₀I
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
      · intro z w1 hzI hzJ hxz hzy hle hGyw1
        have eW1 : w1 = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1 := by
          obtain ⟨hx0, heq0⟩ := hGyw1
          have eL : Power.left (Power.append (fun _ : Fin 1 => m₁) w1) = (fun _ : Fin 1 => m₁) :=
            appendLeftAux _ _
          have eR : Power.right (Power.append (fun _ : Fin 1 => m₁) w1) = w1 :=
            appendRightAux _ _
          calc w1 = Power.right (Power.append (fun _ : Fin 1 => m₁) w1) := eR.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append (fun _ : Fin 1 => m₁) w1)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁) hmI)).1 := by simp only [eL]
        have hzx0 : Lt1 (f.toFun (Subtype.mk z hzI)).1
            (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 := by
          rcases lt_trichotomy (Power.coord1 v₀)
              (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) with h | h | h
          · -- v₀ < f(z): z ∈ S but z < m₁.
            have hzS : S z := by
              rw [hSdef]
              have eLz : Power.left (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) = z :=
                appendLeftAux _ _
              have eRz : Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) =
                  (f.toFun (Subtype.mk z hzI)).1 :=
                appendRightAux _ _
              have hGz : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) :=
                ⟨eLz.symm ▸ hzI, by simp only [eLz, eRz]⟩
              exact ⟨hzJ, hxz, (f.toFun (Subtype.mk z hzI)).1, hGz, h⟩
            have hzLB : LT.lt m₁ (Power.coord1 z) ∨ Power.coord1 z = m₁ :=
              hLBm z hzS
            have hzm : Lt1 z (fun _ => m₁) := hzy
            rcases hzLB with h2 | h2
            · exact False.elim (lt_irrefl _ (lt_trans h2 hzm))
            · have hzm' : LT.lt (Power.coord1 z) m₁ := hzm
              rw [h2] at hzm'
              exact False.elim (lt_irrefl _ hzm')
          · -- v₀ = f(z): z = x₀, contra x₀ < z.
            have heq := h
            exfalso
            have hval : (f.toFun (Subtype.mk z hzI)).1 = v₀ := by
              funext i
              have hiv : i.val < 1 := i.isLt
              have hi0 : i.val = 0 := by omega
              have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
              rw [hi]
              exact heq.symm
            have hsub : (f.toFun (Subtype.mk z hzI)) = (f.toFun (Subtype.mk x₀ hx₀I)) :=
              Subtype.ext (hv₀def ▸ hval)
            have heqZX : z = x₀ := hinj z x₀ hzI hx₀I hsub
            have hcon : Lt1 x₀ x₀ := heqZX ▸ hxz
            exact lt_irrefl _ hcon
          · -- f(z) < v₀: transitivity through f(m₁).
            exact lt_trans h hfmX
        have hgoal : Lt1 (f.toFun (Subtype.mk z hzI)).1 w1 := by
          rw [eW1]
          exact hzx0
        exact hgoal
    -- T₀ is finite: an interval inside would be increasing, contradicting right windows.
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
      have hsub : ∀ x, openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval a b x := by
        intro x hx
        have hxT : T₀ x := hsubAB (hsubUV x hx)
        have hxT' : openInterval a b x ∧ Lt1 x₀ x ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append x w) ∧
              Lt1 v₀ w) ∧
            (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
              Lt1 x₀ z → Lt1 z x →
              (LT.lt (Power.coord1 z) (Power.coord1 x) ∨ Power.coord1 z = Power.coord1 x) →
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x w1) →
              Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) := hxT
        exact hxT'.left
      have hinc : ∀ x (hxI : I x) y (hyI : I y),
          openInterval (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval (Endpoint.finite u) (Endpoint.finite v) y ->
          Lt1 x y → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
        intro x hxI y hyI hjx hjy hxy
        have hyT : T₀ y := hsubAB (hsubUV y hjy)
        have hyT' : openInterval a b y ∧ Lt1 x₀ y ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append y w) ∧
              Lt1 v₀ w) ∧
            (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
              Lt1 x₀ z → Lt1 z y →
              (LT.lt (Power.coord1 z) (Power.coord1 y) ∨ Power.coord1 z = Power.coord1 y) →
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append y w1) →
              Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) := hyT
        obtain ⟨-, -, -, hyU⟩ := hyT'
        have hxT : T₀ x := hsubAB (hsubUV x hjx)
        have hxT' : openInterval a b x ∧ Lt1 x₀ x ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append x w) ∧
              Lt1 v₀ w) ∧
            (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
              Lt1 x₀ z → Lt1 z x →
              (LT.lt (Power.coord1 z) (Power.coord1 x) ∨ Power.coord1 z = Power.coord1 x) →
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x w1) →
              Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) := hxT
        have hxJ : openInterval a b x := hxT'.left
        have hxI' : I x := hsubJ _ hxJ
        have hxx : Lt1 x₀ x := hxT'.right.left
        have eLx : Power.left (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) = y :=
          appendLeftAux _ _
        have eRx : Power.right (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) =
            (f.toFun (Subtype.mk y hyI)).1 :=
          appendRightAux _ _
        have hGy : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y ((f.toFun (Subtype.mk y hyI)).1)) :=
          ⟨eLx.symm ▸ hyI, by simp only [eLx, eRx]⟩
        have hleXY : LT.lt (Power.coord1 x) (Power.coord1 y) ∨
            Power.coord1 x = Power.coord1 y := Or.inl hxy
        exact hyU x _ hxI' hxJ hxx hxy hleXY hGy
      -- Direct contradiction: increasing on (u,v) meets a below-right window.
      have huvlt : LT.lt u v := huv
      obtain ⟨r, hr1, hr2⟩ := exists_between huvlt
      set xp : Power R 1 := fun _ => r with hxpdef
      have hxuv : openInterval (Endpoint.finite u) (Endpoint.finite v) xp := ⟨hr1, hr2⟩
      have hxJ : openInterval a b xp := hsub _ hxuv
      have hxI : I xp := hsubJ _ hxJ
      obtain ⟨c1x, c2x, hc1Jx, hc2Jx, hc1x, hxx2, hleftx, hrightx⟩ :=
        hU xp hxI hxJ
      have hcon : ∀ w : Power R 1, openInterval (Endpoint.finite u) (Endpoint.finite v) w ->
          Lt1 xp w → Lt1 w c2x → False := by
        intro w hjw hxw hwc2
        have hwJ : openInterval a b w := hsub _ hjw
        have hwI : I w := hsubJ _ hwJ
        have hincW : Lt1 (f.toFun (Subtype.mk xp hxI)).1 (f.toFun (Subtype.mk w hwI)).1 :=
          hinc xp hxI w hwI hxuv hjw hxw
        have hwin : Lt1 (f.toFun (Subtype.mk w hwI)).1 (f.toFun (Subtype.mk xp hxI)).1 :=
          hrightx w hwI hwJ hxw hwc2
        exact lt_irrefl _ (lt_trans hincW hwin)
      have hxv : LT.lt (Power.coord1 xp) v := hr2
      have hxc2 : LT.lt (Power.coord1 xp) (Power.coord1 c2x) := hxx2
      obtain ⟨y1, hy1l, hy1r⟩ := exists_between hxc2
      have hrx : LT.lt u (Power.coord1 xp) := hr1
      rcases lt_trichotomy y1 v with h | h | h
      · have hlt1 := h
        have hy1v : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => y1) :=
          ⟨lt_trans hrx hy1l, hlt1⟩
        have hxy1 : Lt1 xp (fun _ => y1) := hy1l
        have hy1c2 : Lt1 (fun _ => y1) c2x := hy1r
        exact hcon _ hy1v hxy1 hy1c2
      · have heq := h
        obtain ⟨y2, hy2l, hy2r⟩ := exists_between hxv
        have hy2v : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => y2) :=
          ⟨lt_trans hrx hy2l, hy2r⟩
        have hxy2 : Lt1 xp (fun _ => y2) := hy2l
        have hy2c2 : Lt1 (fun _ => y2) c2x := by
          have e1 : LT.lt (Power.coord1 (fun _ => y2)) v := hy2r
          rw [← heq] at e1
          exact lt_trans e1 hy1r
        exact hcon _ hy2v hxy2 hy2c2
      · have hlt1 := h
        obtain ⟨y2, hy2l, hy2r⟩ := exists_between hxv
        have hy2v : openInterval (Endpoint.finite u) (Endpoint.finite v) (fun _ => y2) :=
          ⟨lt_trans hrx hy2l, hy2r⟩
        have hxy2 : Lt1 xp (fun _ => y2) := hy2l
        have hy2c2 : Lt1 (fun _ => y2) c2x := lt_trans (lt_trans hy2r hlt1) hy1r
        exact hcon _ hy2v hxy2 hy2c2
    -- Greatest candidate of T₀.
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
    obtain ⟨t₁, ht1Mem, ht1Le⟩ : ∃ t, t ∈ TF ∧ ∀ r ∈ TF, r ≤ t :=
      ⟨TF.max' hTFne, Finset.max'_mem TF hTFne, fun r hr => Finset.le_max' TF r hr⟩
    have ht1Great : ∀ r ∈ TF, LT.lt r t₁ ∨ r = t₁ :=
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
    have ht1x : Lt1 x₀ (fun _ => t₁) := ht1T.right.left
    have ht1I : I (fun _ => t₁) := hsubJ _ ht1J
    have ht1bp : openInterval bp b (fun _ => t₁) := by
      refine ⟨?_, ht1J.right⟩
      exact loTrans bp hx₀mem.left ht1x
    have ht1nL : (fun _ => t₁) ∉ L := hbpNoL _ ht1bp
    set v₁ : Power R 1 := (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 with hv₁def
    set S₁ : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧
      Lt1 (fun _ => t₁) y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 v₁ w) with hS₁def
    -- S(t₁) is nonempty.
    have hNotAll₁ : ¬ ∀ y w v : Power R 1, I y → openInterval a b y → Lt1 (fun _ => t₁) y ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => t₁) v) ->
        Lt1 w v := by
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
    have hyx₂ : Lt1 (fun _ => t₁) y₂ :=
      Classical.byContradiction (fun nb => hv1₂ (fun _ _ b _ _ => absurd b nb))
    have hGyw₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y₂ w₂) :=
      Classical.byContradiction (fun nc => hv1₂ (fun _ _ _ c _ => absurd c nc))
    have hGxv₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append (fun _ => t₁) v₂) :=
      Classical.byContradiction (fun nd => hv1₂ (fun _ _ _ _ d => absurd d nd))
    have hne₂ : ¬ Lt1 w₂ v₂ :=
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
    have hltYX₂ : Lt1 v₁ (f.toFun (Subtype.mk y₂ hyI₂)).1 := by
      have hne₂' : ¬ Lt1 (f.toFun (Subtype.mk y₂ hyI₂)).1 v₁ := by
        rw [hv₁def, ← eV₂, ← eW₂]
        exact hne₂
      rcases lt_trichotomy (Power.coord1 v₁)
          (Power.coord1 ((f.toFun (Subtype.mk y₂ hyI₂)).1)) with h | h | h
      · exact h
      · have heq := h
        exfalso
        have hval : (f.toFun (Subtype.mk y₂ hyI₂)).1 = v₁ := by
          funext i
          have hiv : i.val < 1 := i.isLt
          have hi0 : i.val = 0 := by omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          exact heq.symm
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
    have hSmem₁ : M.S 1 S₁ := abovePreimageDefinable M f a b (fun _ => t₁) ht1I
    have hSne₁ : S₁.Nonempty := ⟨y₂, hSwit₂⟩
    have hBnd₁ : BoundedBelow1 S₁ := by
      refine ⟨t₁, ?_⟩
      intro s hs
      rw [hS₁def] at hs
      obtain ⟨-, hlt, -⟩ := hs
      exact Or.inl hlt
    have hInf₁ := infCompletenessAux S₁ ((M.ominimal _).mp hSmem₁) hSne₁ hBnd₁
    obtain ⟨m₁', hLBm', hGreatestm'⟩ := hInf₁
    obtain ⟨c1t, c2t, hc1Jt, hc2Jt, hc1t, hxt2, hleftt, hrightt⟩ :=
      hU (fun _ => t₁) ht1I ht1J
    have htx2t : LT.lt t₁ (Power.coord1 c2t) := hxt2
    have hc2LB' : IsLowerBound1 S₁ (Power.coord1 c2t) := by
      intro s hs
      rw [hS₁def] at hs
      obtain ⟨hsJ, hsx, hsW⟩ := hs
      obtain ⟨w, hGw, hwlt⟩ := hsW
      rcases lt_trichotomy (Power.coord1 s) (Power.coord1 c2t) with h | h | h
      · have hlt1 := h
        exfalso
        have hsJab : openInterval a b s := hsJ
        have hsI : I s := hsubJ _ hsJab
        have htxt : Lt1 (fun _ => t₁) s := hsx
        have hsc2 : Lt1 s c2t := hlt1
        have hwin : Lt1 (f.toFun (Subtype.mk s hsI)).1 v₁ :=
          hrightt s hsI hsJab htxt hsc2
        have hval : Lt1 v₁ (f.toFun (Subtype.mk s hsI)).1 := by
          have eW : w = (f.toFun (Subtype.mk s hsI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append s w) = s := appendLeftAux _ _
            have eR : Power.right (Power.append s w) = w := appendRightAux _ _
            calc w = Power.right (Power.append s w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append s w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk s hsI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hval hwin)
      · have heq := h
        exact Or.inr heq
      · have hlt2 := h
        exact Or.inl hlt2
    have hmLBc2' : LT.lt (Power.coord1 c2t) m₁' ∨ Power.coord1 c2t = m₁' :=
      hGreatestm' _ hc2LB'
    have hmX' : LT.lt t₁ m₁' := by
      rcases hmLBc2' with h | h
      · exact lt_trans htx2t h
      · rw [← h]
        exact htx2t
    have hmJ' : openInterval a b (fun _ => m₁') := by
      obtain ⟨s0, hs0⟩ := hSne₁
      have hs0' : openInterval a b s0 ∧ Lt1 (fun _ => t₁) s0 ∧
          (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
            (A := I) (B := B) f.toFun (Power.append s0 w) ∧
            Lt1 v₁ w) := by
        rw [hS₁def] at hs0
        exact hs0
      obtain ⟨hs0J, hs0x, -⟩ := hs0'
      have hs0le : LT.lt m₁' (Power.coord1 s0) ∨ Power.coord1 s0 = m₁' :=
        hLBm' s0 hs0
      have haM : Endpoint.lt a (Endpoint.finite m₁') :=
        loTrans a ht1J.left hmX'
      have hMb : Endpoint.lt (Endpoint.finite m₁') b := by
        rcases hs0le with h | h
        · exact hiTrans b hs0J.right h
        · rw [← h]
          exact hs0J.right
      exact ⟨haM, hMb⟩
    have hmI' : I (fun _ => m₁') := hsubJ _ hmJ'
    obtain ⟨c1m', c2m', hc1Jm', hc2Jm', hc1m', hxm2', hleftm', hrightm'⟩ :=
      hU (fun _ => m₁') hmI' hmJ'
    have hfmX' : Lt1 v₁ (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 := by
      by_contra hne
      have hgt : Lt1 (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 v₁ := by
        rcases lt_trichotomy (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁') hmI')).1))
            (Power.coord1 v₁) with h | h | h
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
            exact heq
          have hsub : (f.toFun (Subtype.mk (fun _ => m₁') hmI')) =
              (f.toFun (Subtype.mk (fun _ => t₁) ht1I)) :=
            Subtype.ext hval
          have heqM : (fun _ => m₁') = (fun _ => t₁) := hinj _ _ hmI' ht1I hsub
          have hcon2 : m₁' = t₁ :=
            Eq.trans rfl (congrArg Power.coord1 heqM)
          rw [hcon2] at hmX'
          exact lt_irrefl _ hmX'
        · exact False.elim (hne h)
      have hmc2' : LT.lt m₁' (Power.coord1 c2m') := hxm2'
      obtain ⟨spp, hsppA, hsppt⟩ := notLBofGreatest S₁ m₁' hGreatestm' (Power.coord1 c2m') hmc2'
      have hsppm : LT.lt m₁' (Power.coord1 spp) ∨ Power.coord1 spp = m₁' :=
        hLBm' spp hsppA
      have hspJ : openInterval a b spp := by
        have hspA' : openInterval a b spp ∧ Lt1 (fun _ => t₁) spp ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append spp w) ∧
              Lt1 v₁ w) := hsppA
        exact hspA'.left
      have hspI : I spp := hsubJ _ hspJ
      have hleSP : LT.lt (Power.coord1 spp) (Power.coord1 c2m') := hsppt
      rcases hsppm with h | h
      · -- m₁' < spp: right window gives f(spp) < f(m̂'), but sp ∈ S gives f(t₁) < f(spp) < ... contra hgt.
        have hmsp : Lt1 (fun _ => m₁') spp := h
        have hspc2 : Lt1 spp c2m' := hleSP
        have hfmsp : Lt1 (f.toFun (Subtype.mk spp hspI)).1
            (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 :=
          hrightm' spp hspI hspJ hmsp hspc2
        have hspS : openInterval a b spp ∧ Lt1 (fun _ => t₁) spp ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append spp w) ∧
              Lt1 v₁ w) := hsppA
        obtain ⟨-, hspx, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have hfx : Lt1 v₁ (f.toFun (Subtype.mk spp hspI)).1 := by
          have eW : w = (f.toFun (Subtype.mk spp hspI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append spp w) = spp := appendLeftAux _ _
            have eR : Power.right (Power.append spp w) = w := appendRightAux _ _
            calc w = Power.right (Power.append spp w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append spp w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk spp hspI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact lt_irrefl _ (lt_trans hfx (lt_trans hfmsp hgt))
      · -- spp = m₁' (coords): then spp ∈ S gives f(t₁) < f(m̂'), contra hgt.
        have ept : spp = (fun _ => m₁') := ptEqAux h
        subst ept
        have hspS : openInterval a b (fun _ => m₁') ∧ Lt1 (fun _ => t₁) (fun _ => m₁') ∧
            (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append (fun _ => m₁') w) ∧
              Lt1 v₁ w) := hsppA
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
        exact lt_irrefl _ (lt_trans hwlt hgt)
    -- m₁' is a candidate for t₁.
    set T₁ : Set (Power R 1) := fun y : Power R 1 => openInterval a b y ∧ Lt1 (fun _ => t₁) y ∧
      (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 v₁ w) ∧
      (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
        Lt1 (fun _ => t₁) z → Lt1 z y →
        (LT.lt (Power.coord1 z) (Power.coord1 y) ∨ Power.coord1 z = Power.coord1 y) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) with hT₁def
    have hT₁mem : M.S 1 T₁ := candDefinableR M f a b (fun _ => t₁) ht1I
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
      have hxmM : Lt1 (fun _ => t₁) (fun _ => m₁') := hmX'
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
        have hzt1 : Lt1 (f.toFun (Subtype.mk z hzI)).1
            (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 := by
          rcases lt_trichotomy (Power.coord1 v₁)
              (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) with h | h | h
          · -- v₁ < f(z): z ∈ S₁ but z < m₁'.
            have hzS : S₁ z := by
              rw [hS₁def]
              have eLz : Power.left (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) = z :=
                appendLeftAux _ _
              have eRz : Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) =
                  (f.toFun (Subtype.mk z hzI)).1 :=
                appendRightAux _ _
              have hGz : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) :=
                ⟨eLz.symm ▸ hzI, by simp only [eLz, eRz]⟩
              exact ⟨hzJ, hyz, _, hGz, h⟩
            have hzLB : LT.lt m₁' (Power.coord1 z) ∨ Power.coord1 z = m₁' :=
              hLBm' z hzS
            have hzm : Lt1 z (fun _ => m₁') := hzx
            rcases hzLB with h2 | h2
            · exact False.elim (lt_irrefl _ (lt_trans h2 hzm))
            · have hzm' : LT.lt (Power.coord1 z) m₁' := hzm
              rw [h2] at hzm'
              exact False.elim (lt_irrefl _ hzm')
          · -- v₁ = f(z): z = t₁, contra t₁ < z.
            have heq := h
            exfalso
            have hval : (f.toFun (Subtype.mk z hzI)).1 = v₁ := by
              funext i
              have hiv : i.val < 1 := i.isLt
              have hi0 : i.val = 0 := by omega
              have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
              rw [hi]
              exact heq.symm
            have hsub : (f.toFun (Subtype.mk z hzI)) = (f.toFun (Subtype.mk (fun _ => t₁) ht1I)) :=
              Subtype.ext (hv₁def ▸ hval)
            have heqZX : z = (fun _ => t₁) := hinj z _ hzI ht1I hsub
            have hcon : Lt1 (fun _ => t₁) (fun _ => t₁) := heqZX ▸ hyz
            exact lt_irrefl _ hcon
          · -- f(z) < v₁: transitivity through f(m₁').
            exact lt_trans h hfmX'
        have hgoal : Lt1 (f.toFun (Subtype.mk z hzI)).1 w1 := by
          rw [eW1]
          exact hzt1
        exact hgoal
    -- m₁' lies in T₀ by partition; it is strictly above max T₀: contradiction.
    have hm₁'T₀ : T₀ (fun _ => m₁') := by
      rw [hTdef]
      have hxmM' : Lt1 x₀ (fun _ => m₁') := lt_trans ht1x hmX'
      refine ⟨hmJ', ?_, ?_, ?_⟩
      · exact hxmM'
      · -- f(x₀) < f(m̂') via f(t₁).
        have hft1x : Lt1 v₀ (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := by
          have ht1T' : openInterval a b (fun _ => t₁) ∧ Lt1 x₀ (fun _ => t₁) ∧
              (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                (A := I) (B := B) f.toFun (Power.append (fun _ => t₁) w) ∧
                Lt1 v₀ w) ∧
              (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
                Lt1 x₀ z → Lt1 z (fun _ => t₁) →
                (LT.lt (Power.coord1 z) (Power.coord1 (fun _ => t₁)) ∨
                  Power.coord1 z = Power.coord1 (fun _ => t₁)) →
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => t₁) w1) →
                Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) := ht1T
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
        exact ⟨(f.toFun (Subtype.mk (fun _ => m₁') hmI')).1, hGm, lt_trans hft1x hfmX'⟩
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
        have hgoal : Lt1 (f.toFun (Subtype.mk z hzI)).1 w1 := by
          rw [eW1]
          rcases lt_trichotomy (Power.coord1 z) t₁ with h | h | h
          · -- z < t₁: T₀-universal at t₁, then trans through f(t₁).
            have hlt1 := h
            have hzt1u : Lt1 (f.toFun (Subtype.mk z hzI)).1
                (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := by
              have ht1T' : openInterval a b (fun _ => t₁) ∧ Lt1 x₀ (fun _ => t₁) ∧
                  (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                    (A := I) (B := B) f.toFun (Power.append (fun _ => t₁) w) ∧
                    Lt1 v₀ w) ∧
                  (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
                    Lt1 x₀ z → Lt1 z (fun _ => t₁) →
                    (LT.lt (Power.coord1 z) (Power.coord1 (fun _ => t₁)) ∨
                      Power.coord1 z = Power.coord1 (fun _ => t₁)) →
                    FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                      (Power.append (fun _ => t₁) w1) →
                    Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) := ht1T
              obtain ⟨-, -, -, ht1U⟩ := ht1T'
              have hleTZ : LT.lt (Power.coord1 z) (Power.coord1 (fun _ => t₁)) ∨
                  Power.coord1 z = Power.coord1 (fun _ => t₁) := Or.inl hlt1
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
              have htz : Lt1 z (fun _ => t₁) := hlt1
              have hxz' : Lt1 x₀ z := hyz
              exact ht1U z _ hzI hzJ hxz' htz hleTZ hGt
            exact lt_trans hzt1u hfmX'
          · -- z = t₁: use f(t₁) < f(m₁').
            have heq := h
            have ept : z = (fun _ => t₁) := ptEqAux heq
            subst ept
            exact hfmX'
          · -- z > t₁: T₁-universal gives f(z) < f(m₁') directly.
            have hgt := h
            have hm₁'T₁' : openInterval a b (fun _ => m₁') ∧ Lt1 (fun _ => t₁) (fun _ => m₁') ∧
                (∃ w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                  (A := I) (B := B) f.toFun (Power.append (fun _ => m₁') w) ∧
                  Lt1 v₁ w) ∧
                (∀ z w1 : Power R 1, ∀ hzI : I z, openInterval a b z →
                  Lt1 (fun _ => t₁) z → Lt1 z (fun _ => m₁') →
                  (LT.lt (Power.coord1 z) (Power.coord1 (fun _ => m₁')) ∨
                    Power.coord1 z = Power.coord1 (fun _ => m₁')) →
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => m₁') w1) →
                  Lt1 (f.toFun (Subtype.mk z hzI)).1 w1) := hm₁'T₁
            obtain ⟨-, -, -, hm₁'U⟩ := hm₁'T₁'
            have htz : Lt1 (fun _ => t₁) z := hgt
            have hzx' : Lt1 z (fun _ => m₁') := hzx
            have hleZM : LT.lt (Power.coord1 z) (Power.coord1 (fun _ => m₁')) ∨
                Power.coord1 z = Power.coord1 (fun _ => m₁') :=
              Or.inl hzx
            have eLm' : Power.left (Power.append (fun _ : Fin 1 => m₁')
                ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) = (fun _ : Fin 1 => m₁') :=
              appendLeftAux _ _
            have eRm' : Power.right (Power.append (fun _ : Fin 1 => m₁')
                ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) =
                (f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1 :=
              appendRightAux _ _
            have hGm' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append (fun _ : Fin 1 => m₁') ((f.toFun (Subtype.mk (fun _ : Fin 1 => m₁') hmI')).1)) :=
              ⟨eLm'.symm ▸ hmI', by simp only [eLm', eRm']⟩
            exact hm₁'U z _ hzI hzJ htz hzx' hleZM hGm'
        exact hgoal
    -- Contradiction with maximality of t₁.
    have hmemM : Power.coord1 (fun _ => m₁') ∈ TF := hTFmp _ hm₁'T₀
    have hconGreat : LT.lt (Power.coord1 (fun _ => m₁')) t₁ ∨
        Power.coord1 (fun _ => m₁') = t₁ :=
      ht1Great (Power.coord1 (fun _ => m₁')) hmemM
    have hFalse : False := by
      have hltTM : LT.lt t₁ (Power.coord1 (fun _ => m₁')) := hmX'
      rcases hconGreat with h | h
      · exact lt_irrefl _ (lt_trans hltTM h)
      · exact lt_irrefl _ (h ▸ hltTM)
    exact False.elim hFalse
  · -- Empty window: take (a,b) itself, vacuously decreasing.
    refine ⟨a, b, hlt, hsubJ, ?_⟩
    intro x hxI y hyI hx hy hxy
    exact False.elim (hJne ⟨x, hx⟩)
