-- Prove2me | solution 1 for Monotonicity_Theorem.decreasing_of_uniform_above_below_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-11T15:01:02.658228+00:00
-- url     : https://prove2.me/submissions/a4d6c602-091d-428d-8a4f-674562e489f1

import Definitions.Def_Monotonicity_Theorem_Framework

open Classical
open Monotonicity_Theorem

namespace Monotonicity_Theorem

-- Inlined order-bound infrastructure (verbatim copy of the Bounds definition
-- file, so this public proof needs no private imports).
def NonEmpty1 {R : Type} (A : Set (Power R 1)) : Prop :=
  exists x : Power R 1, A x

def IsUpperBound1 {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1)) (b : R) : Prop :=
  forall x : Power R 1, A x -> (D.lt (Power.coord1 x) b \/ Power.coord1 x = b)

def BoundedAbove1 {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1)) : Prop :=
  exists b : R, IsUpperBound1 D A b

def IsSupremum1 {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1)) (s : R) : Prop :=
  IsUpperBound1 D A s /\
  forall b : R, IsUpperBound1 D A b -> (D.lt s b \/ s = b)

noncomputable def max1 {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (a b : R) : R :=
  if D.lt a b then b else a

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

theorem loTrans {R : Type} (D : DenseLinearOrderNoEndpoints R) (a : Endpoint R)
    {c d : R} (h : Endpoint.lt D a (Endpoint.finite c)) (hlt : D.lt c d) :
    Endpoint.lt D a (Endpoint.finite d) := by
  cases a with
  | negInf => exact trivial
  | finite val => exact D.trans h hlt
  | posInf => exact False.elim h

theorem hiTrans {R : Type} (D : DenseLinearOrderNoEndpoints R) (b : Endpoint R)
    {c d : R} (h : Endpoint.lt D (Endpoint.finite d) b) (hlt : D.lt c d) :
    Endpoint.lt D (Endpoint.finite c) b := by
  cases b with
  | negInf => exact False.elim h
  | finite val => exact D.trans hlt h
  | posInf => exact trivial

theorem allBelow {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {p q r : R} (hpq : D.lt p q) (hpr : D.lt p r) :
    ∃ s : R, D.lt p s ∧ D.lt s q ∧ D.lt s r := by
  obtain ⟨s1, hps1, hs1q⟩ := D.dense hpq
  rcases D.trichotomy s1 r with hlt1 | heq1 | hlt2
  · exact ⟨s1, hps1, hs1q, hlt1.left⟩
  · obtain ⟨heq, -, -⟩ := heq1
    obtain ⟨s2, hps2, hs2⟩ := D.dense hps1
    refine ⟨s2, hps2, D.trans hs2 hs1q, ?_⟩
    rw [← heq]
    exact hs2
  · obtain ⟨hlt, -, -⟩ := hlt2
    obtain ⟨s2, hps2, hs2r⟩ := D.dense hpr
    exact ⟨s2, hps2, D.trans hs2r (D.trans hlt hs1q), hs2r⟩

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
theorem supUnionAux {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (A B : Set (Power R 1)) (sA sB : R)
    (hSupA : IsSupremum1 D A sA)
    (hSupB : IsSupremum1 D B sB) :
    IsSupremum1 D (setUnion A B) (max1 D sA sB) := by
  rcases hSupA with ⟨h_sA_upper, h_sA_least⟩
  rcases hSupB with ⟨h_sB_upper, h_sB_least⟩
  constructor
  · intro x hx
    show D.lt (Power.coord1 x) (if D.lt sA sB then sB else sA) ∨
      Power.coord1 x = (if D.lt sA sB then sB else sA)
    by_cases h : D.lt sA sB
    · rw [if_pos h]
      cases hx with
      | inl hxA =>
        have h1 := h_sA_upper x hxA
        cases h1 with
        | inl hlt => left; exact D.trans hlt h
        | inr heq => left; rw [heq]; exact h
      | inr hxB =>
        exact h_sB_upper x hxB
    · rw [if_neg h]
      cases hx with
      | inl hxA =>
        exact h_sA_upper x hxA
      | inr hxB =>
        have h2 := h_sB_upper x hxB
        rcases D.trichotomy sA sB with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
        · contradiction
        · cases h2 with
          | inl hlt2 => left; rw [heq]; exact hlt2
          | inr heq2 => right; rw [heq]; exact heq2
        · cases h2 with
          | inl hlt2 => left; exact D.trans hlt2 hgt
          | inr heq2 => left; rw [heq2]; exact hgt
  · intro b hb
    have hbA : IsUpperBound1 D A b := fun x hx => hb x (Or.inl hx)
    have hbB : IsUpperBound1 D B b := fun x hx => hb x (Or.inr hx)
    have hA_le_b := h_sA_least b hbA
    have hB_le_b := h_sB_least b hbB
    show D.lt (if D.lt sA sB then sB else sA) b ∨
      (if D.lt sA sB then sB else sA) = b
    by_cases h : D.lt sA sB
    · rw [if_pos h]
      exact hB_le_b
    · rw [if_neg h]
      exact hA_le_b

theorem supOpenIntervalAux {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (a : Endpoint R) (b : R)
    (hNotEmpty : NonEmpty1 (openInterval D a (Endpoint.finite b))) :
    IsSupremum1 D (openInterval D a (Endpoint.finite b)) b := by
  constructor
  · intro x hx
    have hx' : D.lt (Power.coord1 x) b := hx.right
    exact Or.inl hx'
  · intro y hy
    rcases D.trichotomy b y with ⟨hby, _, _⟩ | ⟨heq, _, _⟩ | ⟨hyb, _, _⟩
    · exact Or.inl hby
    · exact Or.inr heq
    · obtain ⟨x0, hx0left, hx0right⟩ := hNotEmpty
      have hm_lt_b : D.lt (max1 D y (Power.coord1 x0)) b := by
        show D.lt (if D.lt y (Power.coord1 x0) then Power.coord1 x0 else y) b
        by_cases h : D.lt y (Power.coord1 x0)
        · rw [if_pos h]
          have hr : D.lt (Power.coord1 x0) b := hx0right
          exact hr
        · rw [if_neg h]
          exact hyb
      obtain ⟨z, hm_lt_z, hz_lt_b⟩ := D.dense hm_lt_b
      have ha_lt_z : Endpoint.lt D a (Endpoint.finite z) := by
        by_cases h : D.lt y (Power.coord1 x0)
        · have hmax : max1 D y (Power.coord1 x0) = Power.coord1 x0 := by
            show (if D.lt y (Power.coord1 x0) then Power.coord1 x0 else y)
              = Power.coord1 x0
            rw [if_pos h]
          rw [hmax] at hm_lt_z
          have hmz : D.lt (Power.coord1 x0) z := hm_lt_z
          cases a with
          | negInf => exact trivial
          | finite val =>
            have g : D.lt val (Power.coord1 x0) := hx0left
            exact D.trans g hmz
          | posInf => exact False.elim hx0left
        · have hx0_le_y : D.lt (Power.coord1 x0) y ∨ Power.coord1 x0 = y := by
            rcases D.trichotomy (Power.coord1 x0) y with ⟨h1, _, _⟩ | ⟨h2, _, _⟩ | ⟨h3, _, _⟩
            · exact Or.inl h1
            · exact Or.inr h2
            · exact absurd h3 h
          have hmax : max1 D y (Power.coord1 x0) = y := by
            show (if D.lt y (Power.coord1 x0) then Power.coord1 x0 else y) = y
            rw [if_neg h]
          rw [hmax] at hm_lt_z
          have hx0_lt_z : D.lt (Power.coord1 x0) z := by
            cases hx0_le_y with
            | inl hlt => exact D.trans hlt hm_lt_z
            | inr heq2 =>
              have hm2 : D.lt y z := hm_lt_z
              rw [heq2]
              exact hm2
          cases a with
          | negInf => exact trivial
          | finite val =>
            have g : D.lt val (Power.coord1 x0) := hx0left
            exact D.trans g hx0_lt_z
          | posInf => exact False.elim hx0left
      have hzmem : openInterval D a (Endpoint.finite b) (fun _ => z) :=
        ⟨ha_lt_z, hz_lt_b⟩
      have hz_le_y := hy (fun _ => z) hzmem
      have hy_lt_z : D.lt y z := by
        by_cases h : D.lt y (Power.coord1 x0)
        · have hmax : max1 D y (Power.coord1 x0) = Power.coord1 x0 := by
            show (if D.lt y (Power.coord1 x0) then Power.coord1 x0 else y)
              = Power.coord1 x0
            rw [if_pos h]
          rw [hmax] at hm_lt_z
          exact D.trans h hm_lt_z
        · have hmax : max1 D y (Power.coord1 x0) = y := by
            show (if D.lt y (Power.coord1 x0) then Power.coord1 x0 else y) = y
            rw [if_neg h]
          rw [hmax] at hm_lt_z
          exact hm_lt_z
      cases hz_le_y with
      | inl hlt =>
        have hlt' : D.lt z y := hlt
        exact False.elim (D.irrefl y (D.trans hy_lt_z hlt'))
      | inr heq =>
        have heq' : z = y := heq
        rw [heq'] at hy_lt_z
        exact False.elim (D.irrefl y hy_lt_z)

theorem supCompletenessAux {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1))
    (hDef : FiniteUnionOfPointsAndIntervals D A)
    (hNotEmpty : NonEmpty1 A)
    (hBounded : BoundedAbove1 D A) :
    ∃ s : R, IsSupremum1 D A s := by
  have hCore : ∀ (A : Set (Power R 1)),
      FiniteUnionOfPointsAndIntervals D A ->
      BoundedAbove1 D A -> (∀ x, ¬ A x) ∨ (∃ s : R, IsSupremum1 D A s) := by
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
        by_cases hEmpty : NonEmpty1 (openInterval D a (Endpoint.finite val))
        · right
          use val
          exact supOpenIntervalAux D a val hEmpty
        · left
          intro x hx
          exact hEmpty ⟨x, hx⟩
      | posInf =>
        cases a with
        | negInf =>
          intro hBounded
          by_cases hEmpty : NonEmpty1 (openInterval D Endpoint.negInf Endpoint.posInf)
          · obtain ⟨x0, -, -⟩ := hEmpty
            rcases hBounded with ⟨M, hM_upper⟩
            obtain ⟨y, hym⟩ := D.no_right_endpoint (max1 D M (Power.coord1 x0))
            have hM_lt_y : D.lt M y := by
              by_cases h : D.lt M (Power.coord1 x0)
              · have hmax : max1 D M (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if D.lt M (Power.coord1 x0) then Power.coord1 x0 else M)
                    = Power.coord1 x0
                  rw [if_pos h]
                rw [hmax] at hym
                exact D.trans h hym
              · have hmax : max1 D M (Power.coord1 x0) = M := by
                  show (if D.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                  rw [if_neg h]
                rw [hmax] at hym
                exact hym
            have hz_gt_a : Endpoint.lt D Endpoint.negInf (Endpoint.finite y) := trivial
            let y_pow : Power R 1 := fun _ => y
            have hy_in : openInterval D Endpoint.negInf Endpoint.posInf y_pow :=
              ⟨hz_gt_a, trivial⟩
            have hy_le_M := hM_upper y_pow hy_in
            cases hy_le_M with
            | inl hlt =>
              exact False.elim (D.irrefl M (D.trans hM_lt_y hlt))
            | inr heq =>
              have heq' : y = M := heq
              rw [heq'] at hM_lt_y
              exact False.elim (D.irrefl M hM_lt_y)
          · left
            intro x hx
            exact hEmpty ⟨x, hx⟩
        | finite val =>
          intro hBounded
          by_cases hEmpty : NonEmpty1 (openInterval D (Endpoint.finite val) Endpoint.posInf)
          · obtain ⟨x0, hx0left, hx0right⟩ := hEmpty
            rcases hBounded with ⟨M, hM_upper⟩
            obtain ⟨y, hym⟩ := D.no_right_endpoint (max1 D M (Power.coord1 x0))
            have hM_lt_y : D.lt M y := by
              by_cases h : D.lt M (Power.coord1 x0)
              · have hmax : max1 D M (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if D.lt M (Power.coord1 x0) then Power.coord1 x0 else M)
                    = Power.coord1 x0
                  rw [if_pos h]
                rw [hmax] at hym
                exact D.trans h hym
              · have hmax : max1 D M (Power.coord1 x0) = M := by
                  show (if D.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                  rw [if_neg h]
                rw [hmax] at hym
                exact hym
            have hx0_gt_a : D.lt val (Power.coord1 x0) := hx0left
            have hz_gt_a : Endpoint.lt D (Endpoint.finite val) (Endpoint.finite y) := by
              by_cases h : D.lt M (Power.coord1 x0)
              · have hmax : max1 D M (Power.coord1 x0) = Power.coord1 x0 := by
                  show (if D.lt M (Power.coord1 x0) then Power.coord1 x0 else M)
                    = Power.coord1 x0
                  rw [if_pos h]
                rw [hmax] at hym
                exact D.trans hx0_gt_a hym
              · have hmin_le : D.lt (Power.coord1 x0) M ∨ Power.coord1 x0 = M := by
                  rcases D.trichotomy (Power.coord1 x0) M with ⟨h1, _, _⟩ | ⟨h2, _, _⟩ | ⟨h3, _, _⟩
                  · exact Or.inl h1
                  · exact Or.inr h2
                  · exact absurd h3 h
                cases hmin_le with
                | inl hlt =>
                  have hmax : max1 D M (Power.coord1 x0) = M := by
                    show (if D.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                    rw [if_neg h]
                  rw [hmax] at hym
                  exact D.trans (D.trans hx0_gt_a hlt) hym
                | inr heq =>
                  have hmax : max1 D M (Power.coord1 x0) = M := by
                    show (if D.lt M (Power.coord1 x0) then Power.coord1 x0 else M) = M
                    rw [if_neg h]
                  rw [hmax] at hym
                  rw [heq] at hx0_gt_a
                  exact D.trans hx0_gt_a hym
            let y_pow : Power R 1 := fun _ => y
            have hy_in : openInterval D (Endpoint.finite val) Endpoint.posInf y_pow :=
              ⟨hz_gt_a, trivial⟩
            have hy_le_M := hM_upper y_pow hy_in
            cases hy_le_M with
            | inl hlt =>
              exact False.elim (D.irrefl M (D.trans hM_lt_y hlt))
            | inr heq =>
              have heq' : y = M := heq
              rw [heq'] at hM_lt_y
              exact False.elim (D.irrefl M hM_lt_y)
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
      have hBoundA : BoundedAbove1 D A := by
        rcases hBounded with ⟨b0, hb0⟩
        exact ⟨b0, fun x hx => hb0 x (Or.inl hx)⟩
      have hBoundB : BoundedAbove1 D B := by
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
            have hbB : IsUpperBound1 D B b := fun x hx => hb x (Or.inr hx)
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
            have hbA : IsUpperBound1 D A b := fun x hx => hb x (Or.inl hx)
            exact hsA_least b hbA
        | inr hSupB =>
          right
          rcases hSupA with ⟨sA, hsA⟩
          rcases hSupB with ⟨sB, hsB⟩
          use max1 D sA sB
          exact supUnionAux D A B sA sB hsA hsB
  cases hCore A hDef hBounded with
  | inl hEmpty =>
    rcases hNotEmpty with ⟨x, hx⟩
    exact False.elim (hEmpty x hx)
  | inr hSup =>
    exact hSup

-- Easy above-below case: uniform local windows with values above on the
-- left and below on the right force a globally decreasing window.
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : forall x y (hx : I x) (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    {a b : Endpoint R} (hsubJ : forall x, openInterval D a b x -> I x)
    (hlt : Endpoint.lt D a b)
    (hU : forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) :
    exists a2 b2 : Endpoint R, Endpoint.lt D a2 b2 /\
      (forall x, openInterval D a2 b2 x -> I x) /\
      (forall x (hxI : I x) y (hyI : I y), openInterval D a2 b2 x -> openInterval D a2 b2 y ->
        Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) := by
  refine ⟨a, b, hlt, hsubJ, ?_⟩
  intro u huI v hvI hJu hJv huv
  have hua : Endpoint.lt D a (Endpoint.finite (u 0)) := hJu.left
  have hub : Endpoint.lt D (Endpoint.finite (u 0)) b := hJu.right
  have hya : Endpoint.lt D a (Endpoint.finite (v 0)) := hJv.left
  have hyb : Endpoint.lt D (Endpoint.finite (v 0)) b := hJv.right
  have hxuv : D.lt (Power.coord1 u) (Power.coord1 v) := huv
  -- Fixed value at u.
  set v0 : Power R 1 := (f.toFun (Subtype.mk u huI)).1 with hv0def
  set v0c : R := Power.coord1 v0 with hv0cdef
  -- The forward set at u.
  set A : Set (Power R 1) := fun s => openInterval D a b s ∧ Lt1 D u s ∧
    forall z (hzI : I z), openInterval D a b z → Lt1 D u z →
      (D.lt (Power.coord1 z) (Power.coord1 s) ∨ Power.coord1 z = Power.coord1 s) →
      Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0 with hAdef
  have hJmem : M.S 1 (openInterval D a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hXGT : M.S 1 (openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hWgt : M.S 1 (openInterval D (Endpoint.finite v0c) Endpoint.posInf) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hWeq : M.S 1 (pointSet v0c) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point v0c)
  have hF : M.S (1 + (1 + 1))
      (fun q : Power R (1 + (1 + 1)) =>
        openInterval D a b (fun i : Fin 1 => q (baS i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baS i)) ∧
        I (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baZ i)) ∧
        (D.lt ((fun j : Fin 2 => q (baLT j)) 0)
          ((fun j : Fin 2 => q (baLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (baG j)) ∧
        (openInterval D (Endpoint.finite v0c) Endpoint.posInf
          (fun i : Fin 1 => q (baW i)) ∨
        pointSet v0c (fun i : Fin 1 => q (baW i)))) :=
    M.inter_mem (M.reindex_mem baS hJmem)
      (M.inter_mem (M.reindex_mem baS hXGT)
        (M.inter_mem (M.reindex_mem baZ f.domain_mem)
          (M.inter_mem (M.reindex_mem baZ hJmem)
            (M.inter_mem (M.reindex_mem baZ hXGT)
              (M.inter_mem
                (M.union_mem (M.reindex_mem baLT M.lt_mem)
                  (M.diagonal_mem (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
                    (⟨1, by decide⟩ : Fin (1 + (1 + 1))) (by decide)))
                (M.inter_mem (M.reindex_mem baG f.graph_mem)
                  (M.union_mem (M.reindex_mem baW hWgt)
                    (M.reindex_mem baW hWeq))))))))
  have hProj : M.S 1 (fun s : Power R 1 => exists t : Power R (1 + 1),
      (fun q : Power R (1 + (1 + 1)) =>
        openInterval D a b (fun i : Fin 1 => q (baS i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baS i)) ∧
        I (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baZ i)) ∧
        (D.lt ((fun j : Fin 2 => q (baLT j)) 0)
          ((fun j : Fin 2 => q (baLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (baG j)) ∧
        (openInterval D (Endpoint.finite v0c) Endpoint.posInf
          (fun i : Fin 1 => q (baW i)) ∨
        pointSet v0c (fun i : Fin 1 => q (baW i))))
        (Power.append s t)) :=
    M.existsLast_mem hF
  have hC : M.S 1 (fun s : Power R 1 => ¬ exists t : Power R (1 + 1),
      (fun q : Power R (1 + (1 + 1)) =>
        openInterval D a b (fun i : Fin 1 => q (baS i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baS i)) ∧
        I (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baZ i)) ∧
        (D.lt ((fun j : Fin 2 => q (baLT j)) 0)
          ((fun j : Fin 2 => q (baLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (baG j)) ∧
        (openInterval D (Endpoint.finite v0c) Endpoint.posInf
          (fun i : Fin 1 => q (baW i)) ∨
        pointSet v0c (fun i : Fin 1 => q (baW i))))
        (Power.append s t)) :=
    M.compl_mem hProj
  have hJX : M.S 1 (setInter (openInterval D a b)
      (openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf)) :=
    M.inter_mem hJmem hXGT
  have hBI : M.S 1 (setInter (setInter (openInterval D a b)
      (openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf))
      (setCompl _)) :=
    M.inter_mem hJX hC
  have heq : (setInter (setInter (openInterval D a b)
      (openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf))
      (setCompl (fun s : Power R 1 => exists t : Power R (1 + 1),
      (fun q : Power R (1 + (1 + 1)) =>
        openInterval D a b (fun i : Fin 1 => q (baS i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baS i)) ∧
        I (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (baZ i)) ∧
        openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
          (fun i : Fin 1 => q (baZ i)) ∧
        (D.lt ((fun j : Fin 2 => q (baLT j)) 0)
          ((fun j : Fin 2 => q (baLT j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (baG j)) ∧
        (openInterval D (Endpoint.finite v0c) Endpoint.posInf
          (fun i : Fin 1 => q (baW i)) ∨
        pointSet v0c (fun i : Fin 1 => q (baW i))))
        (Power.append s t)))) = A := by
    funext s
    apply propext
    constructor
    · intro h
      obtain ⟨hJX, hn0⟩ := h
      obtain ⟨hJs, hXs⟩ := hJX
      have hn : ¬ exists t : Power R (1 + 1),
          (fun q : Power R (1 + (1 + 1)) =>
            openInterval D a b (fun i : Fin 1 => q (baS i)) ∧
            openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
              (fun i : Fin 1 => q (baS i)) ∧
            I (fun i : Fin 1 => q (baZ i)) ∧
            openInterval D a b (fun i : Fin 1 => q (baZ i)) ∧
            openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
              (fun i : Fin 1 => q (baZ i)) ∧
            (D.lt ((fun j : Fin 2 => q (baLT j)) 0)
              ((fun j : Fin 2 => q (baLT j)) 1) ∨
            q (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
              = q (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q (baG j)) ∧
            (openInterval D (Endpoint.finite v0c) Endpoint.posInf
              (fun i : Fin 1 => q (baW i)) ∨
            pointSet v0c (fun i : Fin 1 => q (baW i))))
            (Power.append s t) := hn0
      have hltus : Lt1 D u s := by
        obtain ⟨hlt1, -⟩ := hXs
        exact hlt1
      refine ⟨hJs, hltus, ?_⟩
      intro z hzI hzJ hxz hle
      -- Build the witness value at z.
      have eL : Power.left (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) = z :=
        appendLeftAux _ _
      have eR : Power.right (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) =
          (f.toFun (Subtype.mk z hzI)).1 :=
        appendRightAux _ _
      have hGzw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) :=
        ⟨eL.symm ▸ hzI, by simp only [eL, eR]⟩
      -- Extraction maps for the failure witness.
      have eS : (fun i : Fin 1 => (Power.append s
          (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baS i)) = s := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      have eZ : (fun i : Fin 1 => (Power.append s
          (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baZ i)) = z := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      have eT : (fun j : Fin (1 + 1) => (Power.append s
          (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baG j))
          = Power.append z ((f.toFun (Subtype.mk z hzI)).1) := by
        funext j
        by_cases hj : j.val = 0
        · have e : baG j = (⟨1, by decide⟩ : Fin (1 + (1 + 1))) := by
            simp [baG, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baG j)
              = (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1)))
                (⟨1, by decide⟩ : Fin (1 + (1 + 1))) := by rw [e]
            _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left z _ (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj0]
        · have e : baG j = (⟨2, by decide⟩ : Fin (1 + (1 + 1))) := by
            simp [baG, hj]
          have hjv : j.val = 1 := by omega
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
          calc (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baG j)
              = (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1)))
                (⟨2, by decide⟩ : Fin (1 + (1 + 1))) := by rw [e]
            _ = ((f.toFun (Subtype.mk z hzI)).1) ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1))
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right z _ (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append z ((f.toFun (Subtype.mk z hzI)).1)) j := by rw [hj1]
      -- Trichotomy on values.
      rcases D.trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) v0c with
        hTri | heqC | hgtC
      · have hv : Lt1 D ((f.toFun (Subtype.mk z hzI)).1) v0 := hTri.left
        exact hv
      · obtain ⟨heqV, -, -⟩ := heqC
        exfalso
        apply hn
        use Power.append z ((f.toFun (Subtype.mk z hzI)).1)
        show openInterval D a b (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baS i)) ∧
          openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
            (fun i : Fin 1 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baS i)) ∧
          I (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baZ i)) ∧
          openInterval D a b (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baZ i)) ∧
          openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
            (fun i : Fin 1 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baZ i)) ∧
          (D.lt ((fun j : Fin 2 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baLT j)) 0)
            ((fun j : Fin 2 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baLT j)) 1) ∨
          (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1)))
            (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
            = (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1)))
            (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baG j)) ∧
          (openInterval D (Endpoint.finite v0c) Endpoint.posInf
            (fun i : Fin 1 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baW i)) ∨
          pointSet v0c (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baW i)))
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [eS]
          exact hJs
        · rw [eS]
          obtain ⟨hlt1, hpos⟩ := hXs
          exact ⟨hlt1, hpos⟩
        · rw [eZ]
          exact hzI
        · rw [eZ]
          exact hzJ
        · rw [eZ]
          exact ⟨hxz, trivial⟩
        · cases hle with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h.symm
        · rw [eT]
          exact hGzw
        · exact Or.inr heqV
      · obtain ⟨hgt, -, -⟩ := hgtC
        exfalso
        apply hn
        use Power.append z ((f.toFun (Subtype.mk z hzI)).1)
        show openInterval D a b (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baS i)) ∧
          openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
            (fun i : Fin 1 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baS i)) ∧
          I (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baZ i)) ∧
          openInterval D a b (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baZ i)) ∧
          openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
            (fun i : Fin 1 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baZ i)) ∧
          (D.lt ((fun j : Fin 2 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baLT j)) 0)
            ((fun j : Fin 2 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baLT j)) 1) ∨
          (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1)))
            (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
            = (Power.append s (Power.append z ((f.toFun (Subtype.mk z hzI)).1)))
            (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baG j)) ∧
          (openInterval D (Endpoint.finite v0c) Endpoint.posInf
            (fun i : Fin 1 => (Power.append s
              (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baW i)) ∨
          pointSet v0c (fun i : Fin 1 => (Power.append s
            (Power.append z ((f.toFun (Subtype.mk z hzI)).1))) (baW i)))
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [eS]
          exact hJs
        · rw [eS]
          obtain ⟨hlt1, hpos⟩ := hXs
          exact ⟨hlt1, hpos⟩
        · rw [eZ]
          exact hzI
        · rw [eZ]
          exact hzJ
        · rw [eZ]
          exact ⟨hxz, trivial⟩
        · cases hle with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h.symm
        · rw [eT]
          exact hGzw
        · exact Or.inl ⟨hgt, trivial⟩
    · intro hs
      have hs' : openInterval D a b s ∧ Lt1 D u s ∧
          (forall z (hzI : I z), openInterval D a b z → Lt1 D u z →
            (D.lt (Power.coord1 z) (Power.coord1 s) ∨ Power.coord1 z = Power.coord1 s) →
            Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hs
      obtain ⟨hJs, hltus, hall⟩ := hs'
      have hXs : openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf s :=
        ⟨hltus, trivial⟩
      refine ⟨?_, ?_⟩
      · refine ⟨hJs, hXs⟩
      · show ¬ exists t : Power R (1 + 1),
          (fun q : Power R (1 + (1 + 1)) =>
            openInterval D a b (fun i : Fin 1 => q (baS i)) ∧
            openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
              (fun i : Fin 1 => q (baS i)) ∧
            I (fun i : Fin 1 => q (baZ i)) ∧
            openInterval D a b (fun i : Fin 1 => q (baZ i)) ∧
            openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
              (fun i : Fin 1 => q (baZ i)) ∧
            (D.lt ((fun j : Fin 2 => q (baLT j)) 0)
              ((fun j : Fin 2 => q (baLT j)) 1) ∨
            q (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
              = q (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q (baG j)) ∧
            (openInterval D (Endpoint.finite v0c) Endpoint.posInf
              (fun i : Fin 1 => q (baW i)) ∨
            pointSet v0c (fun i : Fin 1 => q (baW i))))
            (Power.append s t)
        intro hex
        obtain ⟨t, ht⟩ := hex
        have ht' : openInterval D a b (fun i : Fin 1 => (Power.append s t) (baS i)) ∧
            openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
              (fun i : Fin 1 => (Power.append s t) (baS i)) ∧
            I (fun i : Fin 1 => (Power.append s t) (baZ i)) ∧
            openInterval D a b (fun i : Fin 1 => (Power.append s t) (baZ i)) ∧
            openInterval D (Endpoint.finite (Power.coord1 u)) Endpoint.posInf
              (fun i : Fin 1 => (Power.append s t) (baZ i)) ∧
            (D.lt ((fun j : Fin 2 => (Power.append s t) (baLT j)) 0)
              ((fun j : Fin 2 => (Power.append s t) (baLT j)) 1) ∨
            (Power.append s t) (⟨0, by decide⟩ : Fin (1 + (1 + 1)))
              = (Power.append s t) (⟨1, by decide⟩ : Fin (1 + (1 + 1)))) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => (Power.append s t) (baG j)) ∧
            (openInterval D (Endpoint.finite v0c) Endpoint.posInf
              (fun i : Fin 1 => (Power.append s t) (baW i)) ∨
            pointSet v0c (fun i : Fin 1 => (Power.append s t) (baW i))) := ht
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ht'
        set z : Power R 1 := fun _ => (Power.append s t)
          (⟨1, by decide⟩ : Fin (1 + (1 + 1))) with hzdef
        set w : Power R 1 := fun _ => (Power.append s t)
          (⟨2, by decide⟩ : Fin (1 + (1 + 1))) with hwdef
        have eZ' : (fun i : Fin 1 => (Power.append s t) (baZ i)) = z := by
          funext i
          have hiv : i.val < 1 := i.isLt
          have hi0 : i.val = 0 := by omega
          have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
          rw [hi]
          rfl
        have eT' : (fun j : Fin (1 + 1) => (Power.append s t) (baG j))
            = Power.append z w := by
          funext j
          by_cases hj : j.val = 0
          · have e : baG j = (⟨1, by decide⟩ : Fin (1 + (1 + 1))) := by
              simp [baG, hj]
            have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
            calc (Power.append s t) (baG j)
                = (Power.append s t) (⟨1, by decide⟩ : Fin (1 + (1 + 1))) := by rw [e]
              _ = z ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append z w)
                  (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_left z _ (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append z w) j := by rw [hj0]
          · have e : baG j = (⟨2, by decide⟩ : Fin (1 + (1 + 1))) := by
              simp [baG, hj]
            have hjv : j.val = 1 := by omega
            have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hjv
            calc (Power.append s t) (baG j)
                = (Power.append s t) (⟨2, by decide⟩ : Fin (1 + (1 + 1))) := by rw [e]
              _ = w ((⟨0, by decide⟩ : Fin 1)) := rfl
              _ = (Power.append z w)
                  (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                  (Fin.append_right z _ (⟨0, by decide⟩ : Fin 1)).symm
              _ = (Power.append z w) j := by rw [hj1]
        have hzI : I z := by
          rw [← eZ']
          exact h3
        have hzJ : openInterval D a b z := by
          rw [← eZ']
          exact h4
        have hxz : Lt1 D u z := by
          rw [eZ'] at h5
          obtain ⟨hlt1, -⟩ := h5
          exact hlt1
        have hle' : D.lt (Power.coord1 z) (Power.coord1 s) ∨
            Power.coord1 z = Power.coord1 s := by
          rcases h6 with hLT | hEQ
          · exact Or.inl hLT
          · exact Or.inr hEQ.symm
        have hval : Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0 :=
          hall z hzI hzJ hxz hle'
        rw [eT'] at h7
        have eW : w = (f.toFun (Subtype.mk z hzI)).1 := by
          obtain ⟨hx0, heq0⟩ := h7
          have eL0 : Power.left (Power.append z w) = z := appendLeftAux _ _
          have eR0 : Power.right (Power.append z w) = w := appendRightAux _ _
          calc w = Power.right (Power.append z w) := eR0.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append z w)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk z hzI)).1 := by simp only [eL0]
        rcases h8 with hBAD | hBAD
        · obtain ⟨hltW, -⟩ := hBAD
          have hltW' : D.lt v0c (Power.coord1 w) := hltW
          rw [eW] at hltW'
          have hval' : D.lt (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) v0c := hval
          exact D.irrefl _ (D.trans hltW' hval')
        · have heqW : (fun i : Fin 1 => (Power.append s t) (baW i)) 0 = v0c := hBAD
          have heqW' : Power.coord1 w = v0c := heqW
          rw [eW] at heqW'
          have hval' : D.lt (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) v0c := hval
          rw [heqW'] at hval'
          exact D.irrefl _ hval'
  have hAmem : M.S 1 A := by
    rw [← heq]
    exact hBI
  have hJu_probe : openInterval D a b u := hJu
  have hJu2 : openInterval D a b u := hJu
  obtain ⟨c1u, c2u, hc1J, hc2J, hc1u, hxu2, hleft, hright⟩ := hU u huI hJu
  have hxc2 : D.lt (Power.coord1 u) (Power.coord1 c2u) := hxu2
  have notUB : ∀ t : R, ∀ m : R,
      (∀ bnd, IsUpperBound1 D A bnd → (D.lt m bnd ∨ m = bnd)) →
      D.lt t m → ∃ s, A s ∧ D.lt t (Power.coord1 s) := by
    intro t m hLeast htm
    by_contra hne
    have htUB : IsUpperBound1 D A t := by
      intro s hs
      rcases D.trichotomy t (Power.coord1 s) with h | h | h
      · exact False.elim (hne ⟨s, hs, h.left⟩)
      · obtain ⟨heq, -, -⟩ := h
        exact Or.inr heq.symm
      · obtain ⟨hlt2, -, -⟩ := h
        exact Or.inl hlt2
    rcases hLeast t htUB with h | h
    · exact D.irrefl _ (D.trans htm h)
    · rw [h] at htm
      exact D.irrefl _ htm
  cases b with
  | negInf =>
    cases a with
    | negInf => exact False.elim hlt
    | finite _ => exact False.elim hlt
    | posInf => exact False.elim hlt
  | finite bv =>
    obtain ⟨r, hxr, hrc2⟩ := D.dense hxc2
    have hs0 : A (fun _ => r) := by
      have hJr : openInterval D a (Endpoint.finite bv) (fun _ => r) :=
        ⟨loTrans D a hua hxr, hiTrans D (Endpoint.finite bv) hc2J.right hrc2⟩
      have hxs : Lt1 D u (fun _ => r) := hxr
      refine ⟨hJr, hxs, ?_⟩
      intro z hzI hzJ hxz hle
      have hzc2 : Lt1 D z c2u := by
        rcases hle with h | h
        · exact D.trans h hrc2
        · have e : D.lt (Power.coord1 z) (Power.coord1 c2u) := by
            rw [h]
            exact hrc2
          exact e
      exact hright z hzI hzJ hxz hzc2
    have hANE : NonEmpty1 A := ⟨fun _ => r, hs0⟩
    have hAB : BoundedAbove1 D A := by
      refine ⟨bv, ?_⟩
      intro s hs
      have hs' : openInterval D a (Endpoint.finite bv) s ∧ Lt1 D u s ∧
          (forall z (hzI : I z), openInterval D a (Endpoint.finite bv) z → Lt1 D u z →
            (D.lt (Power.coord1 z) (Power.coord1 s) ∨ Power.coord1 z = Power.coord1 s) →
            Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hs
      obtain ⟨hJs, -, -⟩ := hs'
      obtain ⟨-, hhib⟩ := hJs
      exact Or.inl hhib
    have hSup := supCompletenessAux D A
      ((M.ominimal _).mp hAmem) hANE hAB
    obtain ⟨m, hSupm⟩ := hSup
    have hUBm : IsUpperBound1 D A m := hSupm.left
    have hLeastm : ∀ bnd, IsUpperBound1 D A bnd → (D.lt m bnd ∨ m = bnd) := hSupm.right
    have hUBbv : IsUpperBound1 D A bv := by
      intro s hs
      have hs' : openInterval D a (Endpoint.finite bv) s ∧ Lt1 D u s ∧
          (forall z (hzI : I z), openInterval D a (Endpoint.finite bv) z → Lt1 D u z →
            (D.lt (Power.coord1 z) (Power.coord1 s) ∨ Power.coord1 z = Power.coord1 s) →
            Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hs
      obtain ⟨hJs, -, -⟩ := hs'
      obtain ⟨-, hhib⟩ := hJs
      exact Or.inl hhib
    have hmb : m = bv := by
      rcases D.trichotomy m bv with h | h | h
      · obtain ⟨hlt1, -, -⟩ := h
        exfalso
        obtain ⟨s0, hs0⟩ := hANE
        have hs0' : openInterval D a (Endpoint.finite bv) s0 ∧ Lt1 D u s0 ∧
            (forall z (hzI : I z), openInterval D a (Endpoint.finite bv) z → Lt1 D u z →
              (D.lt (Power.coord1 z) (Power.coord1 s0) ∨ Power.coord1 z = Power.coord1 s0) →
              Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hs0
        have hs0J : openInterval D a (Endpoint.finite bv) s0 := hs0'.left
        have hs0x : Lt1 D u s0 := hs0'.right.left
        have hmUB0 : D.lt (Power.coord1 s0) m ∨ Power.coord1 s0 = m := hUBm s0 hs0
        have ham : Endpoint.lt D a (Endpoint.finite m) := by
          rcases hmUB0 with h | h
          · exact loTrans D a hs0J.left h
          · rw [← h]
            exact hs0J.left
        have hmJ : openInterval D a (Endpoint.finite bv) (fun _ => m) :=
          ⟨ham, hlt1⟩
        have hmI : I (fun _ => m) := hsubJ _ hmJ
        obtain ⟨c1m, c2m, hc1Jm, hc2Jm, hc1m, hxm2, hleftm, hrightm⟩ :=
          hU (fun _ => m) hmI hmJ
        have hmc1 : D.lt (Power.coord1 c1m) m := hc1m
        have hmc2 : D.lt m (Power.coord1 c2m) := hxm2
        have hxm : D.lt (Power.coord1 u) m := by
          rcases hmUB0 with h | h
          · exact D.trans hs0x h
          · rw [← h]
            exact hs0x
        obtain ⟨t, htu, htc1, htm⟩ : ∃ t : R, (D.lt (Power.coord1 u) t ∨ Power.coord1 u = t) ∧
            (D.lt (Power.coord1 c1m) t ∨ Power.coord1 c1m = t) ∧ D.lt t m := by
          rcases D.trichotomy (Power.coord1 u) (Power.coord1 c1m) with h | h | h
          · obtain ⟨hlt2, -, -⟩ := h
            exact ⟨Power.coord1 c1m, Or.inl hlt2, Or.inr rfl, hmc1⟩
          · obtain ⟨heq, -, -⟩ := h
            exact ⟨Power.coord1 u, Or.inr rfl, Or.inr heq.symm, hxm⟩
          · obtain ⟨hlt2, -, -⟩ := h
            exact ⟨Power.coord1 u, Or.inr rfl, Or.inl hlt2, hxm⟩
        obtain ⟨spp, hsppA, hsppt⟩ := notUB t m hLeastm htm
        have hsppA' : openInterval D a (Endpoint.finite bv) spp ∧ Lt1 D u spp ∧
            (forall z (hzI : I z), openInterval D a (Endpoint.finite bv) z → Lt1 D u z →
              (D.lt (Power.coord1 z) (Power.coord1 spp) ∨ Power.coord1 z = Power.coord1 spp) →
              Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hsppA
        have hsppJ : openInterval D a (Endpoint.finite bv) spp := hsppA'.left
        have hsppx : Lt1 D u spp := hsppA'.right.left
        have hsppU : forall z (hzI : I z), openInterval D a (Endpoint.finite bv) z → Lt1 D u z →
            (D.lt (Power.coord1 z) (Power.coord1 spp) ∨ Power.coord1 z = Power.coord1 spp) →
            Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0 := hsppA'.right.right
        have hsppI : I spp := hsubJ _ hsppJ
        have hsppm : D.lt (Power.coord1 spp) m ∨ Power.coord1 spp = m := hUBm spp hsppA
        have hleSPP : D.lt (Power.coord1 c1m) (Power.coord1 spp) := by
          rcases htc1 with h | h
          · exact D.trans h hsppt
          · rw [h]
            exact hsppt
        have hUSPP : D.lt (Power.coord1 u) (Power.coord1 spp) := by
          rcases htu with h | h
          · exact D.trans h hsppt
          · rw [h]
            exact hsppt
        have hcrux : Lt1 D (f.toFun (Subtype.mk (fun _ => m) hmI)).1 v0 := by
          rcases hsppm with h | h
          · have hc1spp : Lt1 D c1m spp := hleSPP
            have hsppm' : Lt1 D spp (fun _ => m) := h
            have hfm : Lt1 D (f.toFun (Subtype.mk (fun _ => m) hmI)).1
                (f.toFun (Subtype.mk spp hsppI)).1 :=
              hleftm spp hsppI hsppJ hc1spp hsppm'
            have hxf : Lt1 D (f.toFun (Subtype.mk spp hsppI)).1 v0 :=
              hsppU spp hsppI hsppJ hsppx (Or.inr rfl)
            exact D.trans hfm hxf
          · have ept : spp = (fun _ => m) := ptEqAux h
            subst ept
            exact hsppU (fun _ => m) hmI hmJ hsppx (Or.inr rfl)
        obtain ⟨rr, hrm, hrc2m, hrbvm⟩ := allBelow D hmc2 hlt1
        have hsJ : openInterval D a (Endpoint.finite bv) (fun _ => rr) :=
          ⟨loTrans D a ham hrm, hrbvm⟩
        have hxs' : Lt1 D u (fun _ => rr) := D.trans hxm hrm
        have hsA : A (fun _ => rr) := by
          refine ⟨hsJ, hxs', ?_⟩
          intro z hzI hzJ hxz hleZ
          rcases D.trichotomy (Power.coord1 z) m with h | h | h
          · obtain ⟨hlt2, -, -⟩ := h
            obtain ⟨sss, hsssA, hsssz⟩ := notUB (Power.coord1 z) m hLeastm hlt2
            have hsssA' : openInterval D a (Endpoint.finite bv) sss ∧ Lt1 D u sss ∧
                (forall zw (hzIw : I zw), openInterval D a (Endpoint.finite bv) zw → Lt1 D u zw →
                  (D.lt (Power.coord1 zw) (Power.coord1 sss) ∨ Power.coord1 zw = Power.coord1 sss) →
                  Lt1 D (f.toFun (Subtype.mk zw hzIw)).1 v0) := hsssA
            have hsssU : forall zw (hzIw : I zw), openInterval D a (Endpoint.finite bv) zw → Lt1 D u zw →
                (D.lt (Power.coord1 zw) (Power.coord1 sss) ∨ Power.coord1 zw = Power.coord1 sss) →
                Lt1 D (f.toFun (Subtype.mk zw hzIw)).1 v0 := hsssA'.right.right
            have hleZ' : D.lt (Power.coord1 z) (Power.coord1 sss) ∨
                Power.coord1 z = Power.coord1 sss := Or.inl hsssz
            exact hsssU z hzI hzJ hxz hleZ'
          · obtain ⟨heq, -, -⟩ := h
            have ept : z = (fun _ => m) := ptEqAux heq
            subst ept
            exact hcrux
          · obtain ⟨hgt2, -, -⟩ := h
            have hmz : Lt1 D (fun _ => m) z := hgt2
            have hzc2m : Lt1 D z c2m := by
              rcases hleZ with h | h
              · exact D.trans h hrc2m
              · have e : D.lt (Power.coord1 z) (Power.coord1 c2m) := by
                  rw [h]
                  exact hrc2m
                exact e
            have hfmz : Lt1 D (f.toFun (Subtype.mk z hzI)).1
                (f.toFun (Subtype.mk (fun _ => m) hmI)).1 :=
              hrightm z hzI hzJ hmz hzc2m
            exact D.trans hfmz hcrux
        have hcon : D.lt (Power.coord1 (fun _ => rr)) m ∨
            Power.coord1 (fun _ => rr) = m := hUBm _ hsA
        have hcon2 : D.lt m m := by
          have hrm' : D.lt m (Power.coord1 (fun _ => rr)) := hrm
          rcases hcon with h | h
          · exact D.trans hrm' h
          · rw [h] at hrm'
            exact hrm'
        exact D.irrefl _ hcon2
      · obtain ⟨heq, -, -⟩ := h
        exact heq
      · obtain ⟨hgt, -, -⟩ := h
        exfalso
        rcases hLeastm bv hUBbv with h | h
        · exact D.irrefl _ (D.trans hgt h)
        · rw [h] at hgt
          exact D.irrefl _ hgt
    have hcy : D.lt (Power.coord1 v) m := by
      rw [hmb]
      exact hyb
    obtain ⟨ss, hssA, hssv⟩ := notUB (Power.coord1 v) m hLeastm hcy
    have hssA' : openInterval D a (Endpoint.finite bv) ss ∧ Lt1 D u ss ∧
        (forall z (hzI : I z), openInterval D a (Endpoint.finite bv) z → Lt1 D u z →
          (D.lt (Power.coord1 z) (Power.coord1 ss) ∨ Power.coord1 z = Power.coord1 ss) →
          Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hssA
    have hssU : forall z (hzI : I z), openInterval D a (Endpoint.finite bv) z → Lt1 D u z →
        (D.lt (Power.coord1 z) (Power.coord1 ss) ∨ Power.coord1 z = Power.coord1 ss) →
        Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0 := hssA'.right.right
    have hleV : D.lt (Power.coord1 v) (Power.coord1 ss) ∨
        Power.coord1 v = Power.coord1 ss := Or.inl hssv
    exact hssU v hvI hJv huv hleV
  | posInf =>
    obtain ⟨r, hxr, hrc2⟩ := D.dense hxc2
    have hs0 : A (fun _ => r) := by
      have hJr : openInterval D a Endpoint.posInf (fun _ => r) :=
        ⟨loTrans D a hua hxr, trivial⟩
      have hxs : Lt1 D u (fun _ => r) := hxr
      refine ⟨hJr, hxs, ?_⟩
      intro z hzI hzJ hxz hle
      have hzc2 : Lt1 D z c2u := by
        rcases hle with h | h
        · exact D.trans h hrc2
        · have e : D.lt (Power.coord1 z) (Power.coord1 c2u) := by
            rw [h]
            exact hrc2
          exact e
      exact hright z hzI hzJ hxz hzc2
    have hANE : NonEmpty1 A := ⟨fun _ => r, hs0⟩
    have hUnB : ¬ BoundedAbove1 D A := by
      intro hB
      obtain ⟨bnd, hbnd⟩ := hB
      have hSup := supCompletenessAux D A
        ((M.ominimal _).mp hAmem) hANE ⟨bnd, hbnd⟩
      obtain ⟨m, hSupm⟩ := hSup
      have hUBm : IsUpperBound1 D A m := hSupm.left
      have hLeastm : ∀ bnd, IsUpperBound1 D A bnd → (D.lt m bnd ∨ m = bnd) := hSupm.right
      obtain ⟨s0, hs0m⟩ := hANE
      have hs0' : openInterval D a Endpoint.posInf s0 ∧ Lt1 D u s0 ∧
          (forall z (hzI : I z), openInterval D a Endpoint.posInf z → Lt1 D u z →
            (D.lt (Power.coord1 z) (Power.coord1 s0) ∨ Power.coord1 z = Power.coord1 s0) →
            Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hs0m
      have hs0J : openInterval D a Endpoint.posInf s0 := hs0'.left
      have hs0x : Lt1 D u s0 := hs0'.right.left
      have hmUB0 : D.lt (Power.coord1 s0) m ∨ Power.coord1 s0 = m := hUBm s0 hs0m
      have ham : Endpoint.lt D a (Endpoint.finite m) := by
        rcases hmUB0 with h | h
        · exact loTrans D a hs0J.left h
        · rw [← h]
          exact hs0J.left
      have hmJ : openInterval D a Endpoint.posInf (fun _ => m) := ⟨ham, trivial⟩
      have hmI : I (fun _ => m) := hsubJ _ hmJ
      obtain ⟨c1m, c2m, hc1Jm, hc2Jm, hc1m, hxm2, hleftm, hrightm⟩ :=
        hU (fun _ => m) hmI hmJ
      have hmc1 : D.lt (Power.coord1 c1m) m := hc1m
      have hmc2 : D.lt m (Power.coord1 c2m) := hxm2
      have hxm : D.lt (Power.coord1 u) m := by
        rcases hmUB0 with h | h
        · exact D.trans hs0x h
        · rw [← h]
          exact hs0x
      obtain ⟨t, htu, htc1, htm⟩ : ∃ t : R, (D.lt (Power.coord1 u) t ∨ Power.coord1 u = t) ∧
          (D.lt (Power.coord1 c1m) t ∨ Power.coord1 c1m = t) ∧ D.lt t m := by
        rcases D.trichotomy (Power.coord1 u) (Power.coord1 c1m) with h | h | h
        · obtain ⟨hlt2, -, -⟩ := h
          exact ⟨Power.coord1 c1m, Or.inl hlt2, Or.inr rfl, hmc1⟩
        · obtain ⟨heq, -, -⟩ := h
          exact ⟨Power.coord1 u, Or.inr rfl, Or.inr heq.symm, hxm⟩
        · obtain ⟨hlt2, -, -⟩ := h
          exact ⟨Power.coord1 u, Or.inr rfl, Or.inl hlt2, hxm⟩
      obtain ⟨spp, hsppA, hsppt⟩ := notUB t m hLeastm htm
      have hsppA' : openInterval D a Endpoint.posInf spp ∧ Lt1 D u spp ∧
          (forall z (hzI : I z), openInterval D a Endpoint.posInf z → Lt1 D u z →
            (D.lt (Power.coord1 z) (Power.coord1 spp) ∨ Power.coord1 z = Power.coord1 spp) →
            Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hsppA
      have hsppJ : openInterval D a Endpoint.posInf spp := hsppA'.left
      have hsppx : Lt1 D u spp := hsppA'.right.left
      have hsppU : forall z (hzI : I z), openInterval D a Endpoint.posInf z → Lt1 D u z →
          (D.lt (Power.coord1 z) (Power.coord1 spp) ∨ Power.coord1 z = Power.coord1 spp) →
          Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0 := hsppA'.right.right
      have hsppI : I spp := hsubJ _ hsppJ
      have hsppm : D.lt (Power.coord1 spp) m ∨ Power.coord1 spp = m := hUBm spp hsppA
      have hleSPP : D.lt (Power.coord1 c1m) (Power.coord1 spp) := by
        rcases htc1 with h | h
        · exact D.trans h hsppt
        · rw [h]
          exact hsppt
      have hUSPP : D.lt (Power.coord1 u) (Power.coord1 spp) := by
        rcases htu with h | h
        · exact D.trans h hsppt
        · rw [h]
          exact hsppt
      have hcrux : Lt1 D (f.toFun (Subtype.mk (fun _ => m) hmI)).1 v0 := by
        rcases hsppm with h | h
        · have hc1spp : Lt1 D c1m spp := hleSPP
          have hsppm' : Lt1 D spp (fun _ => m) := h
          have hfm : Lt1 D (f.toFun (Subtype.mk (fun _ => m) hmI)).1
              (f.toFun (Subtype.mk spp hsppI)).1 :=
            hleftm spp hsppI hsppJ hc1spp hsppm'
          have hxf : Lt1 D (f.toFun (Subtype.mk spp hsppI)).1 v0 :=
            hsppU spp hsppI hsppJ hsppx (Or.inr rfl)
          exact D.trans hfm hxf
        · have ept : spp = (fun _ => m) := ptEqAux h
          subst ept
          exact hsppU (fun _ => m) hmI hmJ hsppx (Or.inr rfl)
      obtain ⟨rr, hrm, hrc2m⟩ := D.dense hmc2
      have hsJ : openInterval D a Endpoint.posInf (fun _ => rr) :=
        ⟨loTrans D a ham hrm, trivial⟩
      have hxs' : Lt1 D u (fun _ => rr) := D.trans hxm hrm
      have hsA : A (fun _ => rr) := by
        refine ⟨hsJ, hxs', ?_⟩
        intro z hzI hzJ hxz hleZ
        rcases D.trichotomy (Power.coord1 z) m with h | h | h
        · obtain ⟨hlt2, -, -⟩ := h
          obtain ⟨sss, hsssA, hsssz⟩ := notUB (Power.coord1 z) m hLeastm hlt2
          have hsssA' : openInterval D a Endpoint.posInf sss ∧ Lt1 D u sss ∧
              (forall zw (hzIw : I zw), openInterval D a Endpoint.posInf zw → Lt1 D u zw →
                (D.lt (Power.coord1 zw) (Power.coord1 sss) ∨ Power.coord1 zw = Power.coord1 sss) →
                Lt1 D (f.toFun (Subtype.mk zw hzIw)).1 v0) := hsssA
          have hsssU : forall zw (hzIw : I zw), openInterval D a Endpoint.posInf zw → Lt1 D u zw →
              (D.lt (Power.coord1 zw) (Power.coord1 sss) ∨ Power.coord1 zw = Power.coord1 sss) →
              Lt1 D (f.toFun (Subtype.mk zw hzIw)).1 v0 := hsssA'.right.right
          have hleZ' : D.lt (Power.coord1 z) (Power.coord1 sss) ∨
              Power.coord1 z = Power.coord1 sss := Or.inl hsssz
          exact hsssU z hzI hzJ hxz hleZ'
        · obtain ⟨heq, -, -⟩ := h
          have ept : z = (fun _ => m) := ptEqAux heq
          subst ept
          exact hcrux
        · obtain ⟨hgt2, -, -⟩ := h
          have hmz : Lt1 D (fun _ => m) z := hgt2
          have hzc2m : Lt1 D z c2m := by
            rcases hleZ with h | h
            · exact D.trans h hrc2m
            · have e : D.lt (Power.coord1 z) (Power.coord1 c2m) := by
                rw [h]
                exact hrc2m
              exact e
          have hfmz : Lt1 D (f.toFun (Subtype.mk z hzI)).1
              (f.toFun (Subtype.mk (fun _ => m) hmI)).1 :=
            hrightm z hzI hzJ hmz hzc2m
          exact D.trans hfmz hcrux
      have hcon : D.lt (Power.coord1 (fun _ => rr)) m ∨
          Power.coord1 (fun _ => rr) = m := hUBm _ hsA
      have hcon2 : D.lt m m := by
        have hrm' : D.lt m (Power.coord1 (fun _ => rr)) := hrm
        rcases hcon with h | h
        · exact D.trans hrm' h
        · rw [h] at hrm'
          exact hrm'
      exact D.irrefl _ hcon2
    have hex : ∃ s, A s ∧ D.lt (Power.coord1 v) (Power.coord1 s) := by
      by_contra hne
      apply hUnB
      refine ⟨Power.coord1 v, ?_⟩
      intro s hs
      rcases D.trichotomy (Power.coord1 v) (Power.coord1 s) with h | h | h
      · exact False.elim (hne ⟨s, hs, h.left⟩)
      · obtain ⟨heq, -, -⟩ := h
        exact Or.inr heq.symm
      · obtain ⟨hlt2, -, -⟩ := h
        exact Or.inl hlt2
    obtain ⟨ss, hssA, hssv⟩ := hex
    have hssA' : openInterval D a Endpoint.posInf ss ∧ Lt1 D u ss ∧
        (forall z (hzI : I z), openInterval D a Endpoint.posInf z → Lt1 D u z →
          (D.lt (Power.coord1 z) (Power.coord1 ss) ∨ Power.coord1 z = Power.coord1 ss) →
          Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0) := hssA
    have hssU : forall z (hzI : I z), openInterval D a Endpoint.posInf z → Lt1 D u z →
        (D.lt (Power.coord1 z) (Power.coord1 ss) ∨ Power.coord1 z = Power.coord1 ss) →
        Lt1 D (f.toFun (Subtype.mk z hzI)).1 v0 := hssA'.right.right
    have hleV : D.lt (Power.coord1 v) (Power.coord1 ss) ∨
        Power.coord1 v = Power.coord1 ss := Or.inl hssv
    exact hssU v hvI hJv huv hleV
