-- Prove2me | solution 1 for Monotonicity_Theorem.increasing_of_uniform_above_above_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-11T17:45:43.097337+00:00
-- url     : https://prove2.me/submissions/08167498-9d15-42ce-9a43-1a1cc3d4af90

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval
import Theorems.Thm_Monotonicity_Theorem_incompatible_decreasing_above_above
import Theorems.Thm_Monotonicity_Theorem_incompatible_increasing_above_above
import Theorems.Thm_Monotonicity_Theorem_exists_least_of_list

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

-- Below-sup points exist (from least-upper-bound property).
theorem notUBofLeast {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (A : Set (Power R 1)) (m : R)
    (hLeast : forall bnd, IsUpperBound1 D A bnd -> (D.lt m bnd ∨ m = bnd))
    (t : R) (htm : D.lt t m) : ∃ s, A s ∧ D.lt t (Power.coord1 s) := by
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

-- Finite unions of finite 1-sets are finite.
theorem finiteUnionAux {R : Type} {A B : Set (Power R 1)}
    (hA : IsFinite1 A) (hB : IsFinite1 B) :
    IsFinite1 (setUnion A B) := by
  obtain ⟨LA, hLA⟩ := hA
  obtain ⟨LB, hLB⟩ := hB
  have hmp : ∀ x : Power R 1, setUnion A B x -> Power.coord1 x ∈ LA ++ LB := by
    intro x hx
    cases hx with
    | inl hxA => exact List.mem_append_left LB ((hLA x).mp hxA)
    | inr hxB => exact List.mem_append_right LA ((hLB x).mp hxB)
  have hmpr : ∀ x : Power R 1, Power.coord1 x ∈ LA ++ LB -> setUnion A B x := by
    intro x hx
    cases List.mem_append.mp hx with
    | inl hmA => exact Or.inl ((hLA x).mpr hmA)
    | inr hmB => exact Or.inr ((hLB x).mpr hmB)
  exact ⟨LA ++ LB, fun x => Iff.intro (hmp x) (hmpr x)⟩

-- A nonempty open interval contains a finite-endpoint subwindow.
theorem finiteSubwindow {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {c d : Endpoint R} {p : Power R 1} (hp : openInterval D c d p) :
    ∃ u v : R, D.lt u v ∧
      (forall x, openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
        openInterval D c d x) := by
  obtain ⟨hpc, hpd⟩ := hp
  have hu : ∃ u : R, Endpoint.lt D c (Endpoint.finite u) ∧ D.lt u (Power.coord1 p) := by
    cases c with
    | negInf =>
      obtain ⟨y, hym⟩ := D.no_left_endpoint (Power.coord1 p)
      exact ⟨y, trivial, hym⟩
    | finite val =>
      have hpc' : D.lt val (Power.coord1 p) := hpc
      obtain ⟨y, hy1, hy2⟩ := D.dense hpc'
      exact ⟨y, hy1, hy2⟩
    | posInf => exact False.elim hpc
  have hv : ∃ v : R, D.lt (Power.coord1 p) v ∧ Endpoint.lt D (Endpoint.finite v) d := by
    cases d with
    | negInf => exact False.elim hpd
    | finite val =>
      have hpd' : D.lt (Power.coord1 p) val := hpd
      obtain ⟨y, hy1, hy2⟩ := D.dense hpd'
      exact ⟨y, hy1, hy2⟩
    | posInf =>
      obtain ⟨y, hym⟩ := D.no_right_endpoint (Power.coord1 p)
      exact ⟨y, hym, trivial⟩
  obtain ⟨u, hcu, hup⟩ := hu
  obtain ⟨v, hpv, hvd⟩ := hv
  refine ⟨u, v, D.trans hup hpv, ?_⟩
  intro x hx
  obtain ⟨hxu, hxv⟩ := hx
  have hleft : Endpoint.lt D c (Endpoint.finite (Power.coord1 x)) := by
    cases c with
    | negInf => exact trivial
    | finite val => exact D.trans hcu hxu
    | posInf => exact False.elim hcu
  have hright : Endpoint.lt D (Endpoint.finite (Power.coord1 x)) d := by
    cases d with
    | negInf => exact False.elim hvd
    | finite val => exact D.trans hxv hvd
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
theorem leftMinDefinable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R) :
    M.S 1 (fun x : Power R 1 => openInterval D a b x /\
      forall y w v : Power R 1, I y -> openInterval D a b y -> Lt1 D y x ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) ->
        Lt1 D v w) := by
  have hJmem : M.S 1 (openInterval D a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hF : M.S (1 + (1 + (1 + 1)))
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval D a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval D a b (fun i : Fin 1 => q (lMY i)) ∧
        D.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (D.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
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
  have hProj : M.S 1 (fun x : Power R 1 => exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval D a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval D a b (fun i : Fin 1 => q (lMY i)) ∧
        D.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (D.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)) :=
    M.existsLast_mem hF
  have hC : M.S 1 (fun x : Power R 1 => ¬ exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval D a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval D a b (fun i : Fin 1 => q (lMY i)) ∧
        D.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (D.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)) :=
    M.compl_mem hProj
  have hJX : M.S 1 (setInter (openInterval D a b)
      (fun x : Power R 1 => ¬ exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval D a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval D a b (fun i : Fin 1 => q (lMY i)) ∧
        D.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (D.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t))) :=
    M.inter_mem hJmem hC
  have heq : (setInter (openInterval D a b)
      (fun x : Power R 1 => ¬ exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        openInterval D a b (fun i : Fin 1 => q (lMX i)) ∧
        I (fun i : Fin 1 => q (lMY i)) ∧
        openInterval D a b (fun i : Fin 1 => q (lMY i)) ∧
        D.lt ((fun j : Fin 2 => q (lMLT j)) 0)
          ((fun j : Fin 2 => q (lMLT j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGW j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (lMGX j)) ∧
        (D.lt ((fun j : Fin 2 => q (lMBAD j)) 0)
          ((fun j : Fin 2 => q (lMBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append x t)))
      = (fun x : Power R 1 => openInterval D a b x /\
        forall y w v : Power R 1, I y -> openInterval D a b y -> Lt1 D y x ->
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w) ->
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x v) ->
          Lt1 D v w) := by
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
      have gXY : D.lt ((fun j : Fin 2 => (Power.append x
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
      have hJY : openInterval D a b (fun i : Fin 1 => (Power.append x
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
      cases D.trichotomy (Power.coord1 v) (Power.coord1 w) with
      | inl hTri =>
        exact hTri.left
      | inr h =>
        cases h with
        | inl h =>
          have gEq : (Power.append x (Power.append y (Power.append w v)))
                (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
              = (Power.append x (Power.append y (Power.append w v)))
                (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1)))) := h.left.symm
          exact False.elim (hn ⟨Power.append y (Power.append w v),
            hJx, hIY, hJY, gXY, hGW, hGX, Or.inr gEq⟩)
        | inr h =>
          have gLt : D.lt ((fun j : Fin 2 => (Power.append x
                  (Power.append y (Power.append w v))) (lMBAD j)) 0)
              ((fun j : Fin 2 => (Power.append x
                  (Power.append y (Power.append w v))) (lMBAD j)) 1) := h.left
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
      have hyJ : openInterval D a b y := by
        rw [← eY']
        exact hJyF
      have hxy : Lt1 D y x := hLT
      have hGyw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) := by
        rw [← eGWt]
        exact hGW
      have hGxv : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) := by
        rw [← eGXt]
        exact hGX
      have hval : Lt1 D v w := hall y w v hy hyJ hxy hGyw hGxv
      rcases hBad with hLT2 | hEQ
      · have hval' : D.lt (Power.coord1 v) (Power.coord1 w) := hval
        have hlt2' : D.lt (Power.coord1 w) (Power.coord1 v) := hLT2
        exact D.irrefl _ (D.trans hval' hlt2')
      · have heq' : Power.coord1 w = Power.coord1 v := hEQ
        have hval' : D.lt (Power.coord1 v) (Power.coord1 w) := hval
        rw [heq'] at hval'
        exact D.irrefl _ hval'
  rw [← heq]
  exact hJX

-- Values below a fixed bound attained on a window: preimage is definable.
theorem belowPreimageDefinable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R)
    (x₀ : Power R 1) (hx₀I : I x₀) :
    M.S 1 (fun y : Power R 1 => openInterval D a b y ∧
      Lt1 D y x₀ ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1)) := by
  have hJmem : M.S 1 (openInterval D a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hXLT : M.S 1 (openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hW : M.S 1 (openInterval D Endpoint.negInf
      (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hG2 : M.S (1 + 1)
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval D Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i))) :=
    M.inter_mem f.graph_mem (M.reindex_mem preW hW)
  have hPRE : M.S 1 (fun y : Power R 1 => exists w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval D Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w)) :=
    M.existsLast_mem hG2
  have hS : M.S 1 (setInter (setInter (openInterval D a b)
      (openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))))
      (fun y : Power R 1 => exists w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval D Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w))) :=
    M.inter_mem (M.inter_mem hJmem hXLT) hPRE
  have heqS : (setInter (setInter (openInterval D a b)
      (openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))))
      (fun y : Power R 1 => exists w : Power R 1,
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun q ∧
        openInterval D Endpoint.negInf
          (Endpoint.finite (Power.coord1 ((f.toFun (Subtype.mk x₀ hx₀I)).1)))
          (fun i : Fin 1 => q (preW i)))
        (Power.append y w)))
      = (fun y : Power R 1 => openInterval D a b y ∧
        Lt1 D y x₀ ∧
        (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1)) := by
    funext y
    apply propext
    constructor
    · intro h
      obtain ⟨hJX, hRest⟩ := h
      obtain ⟨hJy, hXy⟩ := hJX
      obtain ⟨w, hG, hWlt⟩ := hRest
      have hxy : Lt1 D y x₀ := by
        obtain ⟨-, hlt1⟩ := hXy
        exact hlt1
      have hwlt : Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1 := by
        obtain ⟨-, hlt1⟩ := hWlt
        exact hlt1
      exact ⟨hJy, hxy, ⟨w, hG, hwlt⟩⟩
    · intro h
      obtain ⟨hJy, hxy, hPREw⟩ := h
      obtain ⟨w, hG, hwlt⟩ := hPREw
      have hXy : openInterval D Endpoint.negInf
          (Endpoint.finite (Power.coord1 x₀)) y := ⟨trivial, hxy⟩
      have hWlt : openInterval D Endpoint.negInf
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
theorem candDefinable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (a b : Endpoint R)
    (x₀ : Power R 1) (hx₀I : I x₀) :
    M.S 1 (fun y : Power R 1 => openInterval D a b y ∧ Lt1 D y x₀ ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
      (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
        Lt1 D y z → Lt1 D z x₀ →
        (D.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1)) := by
  have hJmem : M.S 1 (openInterval D a b) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a b)
  have hXz : M.S 1 (openInterval D Endpoint.negInf
      (Endpoint.finite (Power.coord1 x₀))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hPREfull : M.S 1 (fun y : Power R 1 => openInterval D a b y ∧
      Lt1 D y x₀ ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1)) :=
    belowPreimageDefinable D M f a b x₀ hx₀I
  have hF : M.S (1 + (1 + (1 + 1)))
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (D.lt ((fun j : Fin 2 => q (tBAD j)) 0)
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
  have hProj : M.S 1 (fun y : Power R 1 => exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (D.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)) :=
    M.existsLast_mem hF
  have hC : M.S 1 (fun y : Power R 1 => ¬ exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (D.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)) :=
    M.compl_mem hProj
  have hPREfull : M.S 1 (fun y : Power R 1 => openInterval D a b y ∧
      Lt1 D y x₀ ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1)) :=
    belowPreimageDefinable D M f a b x₀ hx₀I
  have hTmem : M.S 1 (setInter
      (fun y : Power R 1 => openInterval D a b y ∧
        Lt1 D y x₀ ∧
        (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1))
      (fun y : Power R 1 => ¬ exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (D.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t))) :=
    M.inter_mem hPREfull hC
  have heqT : (setInter
      (fun y : Power R 1 => openInterval D a b y ∧
        Lt1 D y x₀ ∧
        (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1))
      (fun y : Power R 1 => ¬ exists t : Power R (1 + (1 + 1)),
      (fun q : Power R (1 + (1 + (1 + 1))) =>
        I (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D a b (fun i : Fin 1 => q (tCZ i)) ∧
        openInterval D Endpoint.negInf (Endpoint.finite (Power.coord1 x₀))
          (fun i : Fin 1 => q (tCZ i)) ∧
        D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∧
        (D.lt ((fun j : Fin 2 => q (tLTyz j)) 0)
          ((fun j : Fin 2 => q (tLTyz j)) 1) ∨
        q (⟨0, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨1, by decide⟩ : Fin (1 + (1 + (1 + 1))))) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG1 j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (tG2 j)) ∧
        (D.lt ((fun j : Fin 2 => q (tBAD j)) 0)
          ((fun j : Fin 2 => q (tBAD j)) 1) ∨
        q (⟨2, by decide⟩ : Fin (1 + (1 + (1 + 1))))
          = q (⟨3, by decide⟩ : Fin (1 + (1 + (1 + 1))))))
        (Power.append y t)))
      = (fun y : Power R 1 => openInterval D a b y ∧ Lt1 D y x₀ ∧
        (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
          (A := I) (B := B) f.toFun (Power.append y w) ∧
          Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
        (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
          Lt1 D y z → Lt1 D z x₀ →
          (D.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w1) →
          Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1)) := by
    funext y
    apply propext
    constructor
    · intro h
      obtain ⟨hPRE, hn⟩ := h
      obtain ⟨hJy, hXy, hPREw⟩ := hPRE
      obtain ⟨wY, hGY, hWlt⟩ := hPREw
      have hltYX : Lt1 D y x₀ := hXy
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
      rcases D.trichotomy (Power.coord1 w1)
          (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) with
        hTri | heqC | hgtC
      · have hv : Lt1 D w1 ((f.toFun (Subtype.mk z hzI)).1) := hTri.left
        exact hv
      · obtain ⟨heqV, -, -⟩ := heqC
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
      · obtain ⟨hgt, -, -⟩ := hgtC
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
        have hzJ : openInterval D a b z := by
          rw [← eZt]
          exact hJz
        have hyz : Lt1 D y z := hLT
        have hzx : Lt1 D z x₀ := by
          rw [eZt] at hXz
          obtain ⟨-, hlt1⟩ := hXz
          exact hlt1
        have hleYZ : D.lt (Power.coord1 y) (Power.coord1 z) ∨
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
        have hval : Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1 :=
          hall z w1 hzI hzJ hyz hzx hleYZ hGyw1
        have eW : w2 = (f.toFun (Subtype.mk z hzI)).1 := by
          obtain ⟨hx0, heq0⟩ := hGzw2
          have eL0 : Power.left (Power.append z w2) = z := appendLeftAux _ _
          have eR0 : Power.right (Power.append z w2) = w2 := appendRightAux _ _
          calc w2 = Power.right (Power.append z w2) := eR0.symm
            _ = (f.toFun (Subtype.mk (Power.left (Power.append z w2)) hx0)).1 := heq0
            _ = (f.toFun (Subtype.mk z hzI)).1 := by simp only [eL0]
        rcases hBAD with hBADlt | hBADeq
        · have hLT2' : D.lt (Power.coord1 w2) (Power.coord1 w1) := hBADlt
          have hval' : D.lt (Power.coord1 w1)
              (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) := hval
          rw [eW] at hLT2'
          exact D.irrefl _ (D.trans hval' hLT2')
        · have heq' : Power.coord1 w1 = Power.coord1 w2 := hBADeq
          have hval' : D.lt (Power.coord1 w1)
              (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1)) := hval
          rw [eW] at heq'
          rw [heq'] at hval'
          exact D.irrefl _ hval'
  rw [← heqT]
  exact hTmem

open Monotonicity_Theorem

-- Difficult above_above case: uniform valleys are impossible for injective f.
-- Derive False via left-global minima, candidate suprema, and nested minima.
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
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) :
    exists a2 b2 : Endpoint R, Endpoint.lt D a2 b2 /\
      (forall x, openInterval D a2 b2 x -> I x) /\
      (forall x (hxI : I x) y (hyI : I y), openInterval D a2 b2 x -> openInterval D a2 b2 y ->
        Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) := by
  by_cases hJne : NonEmpty1 (openInterval D a b)
  · -- Nonempty window: derive False.
    set L : Set (Power R 1) := fun x : Power R 1 => openInterval D a b x /\
      forall y w v : Power R 1, I y -> openInterval D a b y -> Lt1 D y x ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x v) ->
        Lt1 D v w with hLdef
    have hLmem : M.S 1 L := leftMinDefinable D M f a b
    have hLfin : IsFinite1 L := by
      by_contra hne
      have hInf : IsInfinite1 L := hne
      obtain ⟨a', b', hltAB, hsubAB⟩ :=
        Monotonicity_Theorem.infinite_definable_set_contains_interval D M L hLmem hInf
      have hJne' : NonEmpty1 (openInterval D a' b') := by
        cases a' with
        | negInf =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val =>
            obtain ⟨y, hym⟩ := D.no_left_endpoint val
            exact ⟨fun _ => y, trivial, hym⟩
          | posInf =>
            have xJex : ∃ x : Power R 1, openInterval D a b x := hJne
            obtain ⟨xJ, -⟩ := xJex
            exact ⟨xJ, trivial, trivial⟩
        | finite val =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val2 =>
            obtain ⟨y, hy1, hy2⟩ := D.dense hltAB
            exact ⟨fun _ => y, hy1, hy2⟩
          | posInf =>
            obtain ⟨y, hym⟩ := D.no_right_endpoint val
            exact ⟨fun _ => y, hym, trivial⟩
        | posInf => exact False.elim hltAB
      obtain ⟨p, hp⟩ := hJne'
      obtain ⟨u, v, huv, hsubUV⟩ := finiteSubwindow D hp
      have hsub : forall x, openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval D a b x := by
        intro x hx
        have hLx : L x := hsubAB (hsubUV x hx)
        exact hLx.left
      have hdec : forall x (hxI : I x) y (hyI : I y),
          openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
          Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
        intro x hxI y hyI hjx hjy hxy
        have hyL : L y := hsubAB (hsubUV y hjy)
        have hyL' : openInterval D a b y ∧
            (forall y0 w v : Power R 1, I y0 -> openInterval D a b y0 -> Lt1 D y0 y ->
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append y0 w) ->
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append y v) ->
              Lt1 D v w) := hyL
        have hallY : forall y0 w v : Power R 1, I y0 -> openInterval D a b y0 -> Lt1 D y0 y ->
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y0 w) ->
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y v) ->
            Lt1 D v w := hyL'.right
        have hxJab : openInterval D a b x := hsub _ hjx
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
      exact Monotonicity_Theorem.incompatible_decreasing_above_above D M f
        hsubJ hU huv hsub hdec
    -- Base right endpoint: min of L, or b if L is empty.
    obtain ⟨Lst, hLst⟩ := hLfin
    have ha' : ∃ ap : Endpoint R, Endpoint.lt D a ap ∧
        (∀ x, openInterval D a ap x → x ∉ L) ∧
        (∀ x, openInterval D a ap x → openInterval D a b x) := by
      by_cases hLstNe : Lst = []
      · refine ⟨b, hlt, ?_, ?_⟩
        · intro x hx hxL
          have hmem : Power.coord1 x ∈ Lst := (hLst x).mp hxL
          rw [hLstNe] at hmem
          simp at hmem
        · intro x hx
          exact hx
      · obtain ⟨m, hmMem, hmLeast⟩ :=
          Monotonicity_Theorem.exists_least_of_list D Lst hLstNe
        have hxStar : L (fun _ => m) := (hLst _).mpr hmMem
        have hJstar : openInterval D a b (fun _ => m) := hxStar.left
        have ham' : Endpoint.lt D a (Endpoint.finite m) := hJstar.left
        have hmb' : Endpoint.lt D (Endpoint.finite m) b := hJstar.right
        refine ⟨Endpoint.finite m, ham', ?_, ?_⟩
        · intro x hx hxL
          have hmem : Power.coord1 x ∈ Lst := (hLst x).mp hxL
          have hle := hmLeast (Power.coord1 x) hmem
          have hltxm : D.lt (Power.coord1 x) m := hx.right
          rcases hle with h | h
          · exact D.irrefl _ (D.trans hltxm h)
          · rw [h] at hltxm
            exact D.irrefl _ hltxm
        · intro x hx
          obtain ⟨hxlo, hxhi⟩ := hx
          refine ⟨hxlo, ?_⟩
          exact hiTrans D b hmb' hxhi
    obtain ⟨ap, hapLt, hapNoL, hapSub⟩ := ha'
    -- Witness x₀ in (a, ap).
    have hAne : NonEmpty1 (openInterval D a ap) := by
      cases ap with
      | negInf =>
        cases a with
        | negInf => exact False.elim hapLt
        | finite _ => exact False.elim hapLt
        | posInf => exact False.elim hapLt
      | finite val =>
        cases a with
        | negInf =>
          obtain ⟨y, hym⟩ := D.no_left_endpoint val
          exact ⟨fun _ => y, trivial, hym⟩
        | finite val2 =>
          have hlt2 : D.lt val2 val := hapLt
          obtain ⟨y, hy1, hy2⟩ := D.dense hlt2
          exact ⟨fun _ => y, hy1, hy2⟩
        | posInf => exact False.elim hapLt
      | posInf =>
        obtain ⟨xJ, hxJ⟩ := hJne
        obtain ⟨hxlo, -⟩ := hxJ
        exact ⟨xJ, hxlo, trivial⟩
    obtain ⟨x₀, hx₀mem⟩ := hAne
    have hx₀J : openInterval D a b x₀ := hapSub _ hx₀mem
    have hx₀nL : x₀ ∉ L := hapNoL _ hx₀mem
    have hx₀I : I x₀ := hsubJ _ hx₀J
    set v₀ : Power R 1 := (f.toFun (Subtype.mk x₀ hx₀I)).1 with hv₀def
    set S : Set (Power R 1) := fun y : Power R 1 => openInterval D a b y ∧
      Lt1 D y x₀ ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w v₀) with hSdef
    -- S(x₀) is nonempty: x₀ is not a left-global minimum.
    have hNotAll : ¬ forall y w v : Power R 1, I y -> openInterval D a b y -> Lt1 D y x₀ ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x₀ v) ->
        Lt1 D v w := by
      intro hall
      apply hx₀nL
      rw [hLdef]
      exact ⟨hx₀J, hall⟩
    obtain ⟨y, hy1⟩ := Classical.not_forall.mp hNotAll
    obtain ⟨w, hw1⟩ := Classical.not_forall.mp hy1
    obtain ⟨v, hv1⟩ := Classical.not_forall.mp hw1
    have hyI : I y :=
      Classical.byContradiction (fun na => hv1 (fun a _ _ _ _ => absurd a na))
    have hyJ : openInterval D a b y :=
      Classical.byContradiction (fun na => hv1 (fun _ a _ _ _ => absurd a na))
    have hyx : Lt1 D y x₀ :=
      Classical.byContradiction (fun nb => hv1 (fun _ _ b _ _ => absurd b nb))
    have hGyw : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y w) :=
      Classical.byContradiction (fun nc => hv1 (fun _ _ _ c _ => absurd c nc))
    have hGxv : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append x₀ v) :=
      Classical.byContradiction (fun nd => hv1 (fun _ _ _ _ d => absurd d nd))
    have hne : ¬ Lt1 D v w :=
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
    have hltYX : Lt1 D (f.toFun (Subtype.mk y hyI)).1 v₀ := by
      have hne' : ¬ Lt1 D v₀ (f.toFun (Subtype.mk y hyI)).1 := by
        rw [hv₀def, ← eV, ← eW]
        exact hne
      rcases D.trichotomy (Power.coord1 ((f.toFun (Subtype.mk y hyI)).1))
          (Power.coord1 v₀) with h | h | h
      · exact h.left
      · obtain ⟨heq, -, -⟩ := h
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
        have hcon : Lt1 D x₀ x₀ := heqYX ▸ hyx
        exact False.elim (D.irrefl _ hcon)
      · exact False.elim (hne' h.left)
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
    have hSmem : M.S 1 S := belowPreimageDefinable D M f a b x₀ hx₀I
    have hSne : NonEmpty1 S := ⟨y, hSwit⟩
    have hBnd : BoundedAbove1 D S := by
      refine ⟨Power.coord1 x₀, ?_⟩
      intro s hs
      rw [hSdef] at hs
      obtain ⟨-, hlt, -⟩ := hs
      exact Or.inl hlt
    have hSup := supCompletenessAux D S ((M.ominimal _).mp hSmem) hSne hBnd
    obtain ⟨m₁, hUBm, hLeastm⟩ := hSup
    -- m₁ is strictly left of x₀ (S avoids the left window).
    obtain ⟨c1x, c2x, hc1Jx, hc2Jx, hc1x, hxx2, hleftx, hrightx⟩ :=
      hU x₀ hx₀I hx₀J
    have hmc1x : D.lt (Power.coord1 c1x) (Power.coord1 x₀) := hc1x
    have hc1UB : IsUpperBound1 D S (Power.coord1 c1x) := by
      intro s hs
      rw [hSdef] at hs
      obtain ⟨hsJ, hsx, hsW⟩ := hs
      obtain ⟨w, hGw, hwlt⟩ := hsW
      rcases D.trichotomy (Power.coord1 c1x) (Power.coord1 s) with h | h | h
      · obtain ⟨hlt1, -, -⟩ := h
        exfalso
        have hsJab : openInterval D a b s := hsJ
        have hsI : I s := hsubJ _ hsJab
        have hsc1 : Lt1 D c1x s := hlt1
        have hsx0 : Lt1 D s x₀ := hsx
        have hwin : Lt1 D v₀ (f.toFun (Subtype.mk s hsI)).1 :=
          hleftx s hsI hsJab hsc1 hsx0
        have hval : Lt1 D (f.toFun (Subtype.mk s hsI)).1 v₀ := by
          have eW : w = (f.toFun (Subtype.mk s hsI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append s w) = s := appendLeftAux _ _
            have eR : Power.right (Power.append s w) = w := appendRightAux _ _
            calc w = Power.right (Power.append s w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append s w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk s hsI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact D.irrefl _ (D.trans hwin hval)
      · obtain ⟨heq, -, -⟩ := h
        exact Or.inr heq.symm
      · obtain ⟨hlt2, -, -⟩ := h
        exact Or.inl hlt2
    have hmUBc1 : D.lt m₁ (Power.coord1 c1x) ∨ m₁ = Power.coord1 c1x :=
      hLeastm _ hc1UB
    have hmX : D.lt m₁ (Power.coord1 x₀) := by
      rcases hmUBc1 with h | h
      · exact D.trans h hmc1x
      · rw [h]
        exact hmc1x
    have hmJ : openInterval D a b (fun _ => m₁) := by
      obtain ⟨s0, hs0⟩ := hSne
      have hs0' : openInterval D a b s0 ∧ Lt1 D s0 x₀ ∧
          (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
            (A := I) (B := B) f.toFun (Power.append s0 w) ∧
            Lt1 D w v₀) := by
        rw [hSdef] at hs0
        exact hs0
      obtain ⟨hs0J, hs0x, -⟩ := hs0'
      have hs0le : D.lt (Power.coord1 s0) m₁ ∨ Power.coord1 s0 = m₁ :=
        hUBm s0 hs0
      have haM : Endpoint.lt D a (Endpoint.finite m₁) := by
        rcases hs0le with h | h
        · exact loTrans D a hs0J.left h
        · rw [← h]
          exact hs0J.left
      have hMb : Endpoint.lt D (Endpoint.finite m₁) b :=
        hiTrans D b hx₀J.right hmX
      exact ⟨haM, hMb⟩
    have hmI : I (fun _ => m₁) := hsubJ _ hmJ
    obtain ⟨c1m, c2m, hc1Jm, hc2Jm, hc1m, hxm2, hleftm, hrightm⟩ :=
      hU (fun _ => m₁) hmI hmJ
    -- f(m₁) < f(x₀): else the left window at m₁ contradicts maximality.
    have hfmX : Lt1 D (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 v₀ := by
      by_contra hne
      have hgt : Lt1 D v₀ (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1 := by
        rcases D.trichotomy (Power.coord1 v₀)
            (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁) hmI)).1)) with h | h | h
        · exact h.left
        · obtain ⟨heq, -, -⟩ := h
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
          exact D.irrefl _ hmX
        · exact False.elim (hne h.left)
      obtain ⟨c1m, c2m, hc1Jm, hc2Jm, hc1m, hxm2, hleftm, hrightm⟩ :=
        hU (fun _ => m₁) hmI hmJ
      have hmc1 : D.lt (Power.coord1 c1m) m₁ := hc1m
      obtain ⟨sp, hspA, hsppt⟩ := notUBofLeast D S m₁ hLeastm (Power.coord1 c1m) hmc1
      -- sp ∈ S above c1m; sp ≤ m₁; case split
      have hsppm : D.lt (Power.coord1 sp) m₁ ∨ Power.coord1 sp = m₁ :=
        hUBm sp hspA
      have hspJ : openInterval D a b sp := by
        have hspA' : openInterval D a b sp ∧ Lt1 D sp x₀ ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append sp w) ∧
              Lt1 D w v₀) := hspA
        exact hspA'.left
      have hspI : I sp := hsubJ _ hspJ
      have hleSP : D.lt (Power.coord1 c1m) (Power.coord1 sp) := hsppt
      rcases hsppm with h | h
      · -- sp < m₁: left window gives f(m̂) < f(sp), but sp ∈ S gives f(sp) < f(x₀) < f(m̂).
        have hc1sp : Lt1 D c1m sp := hleSP
        have hspm : Lt1 D sp (fun _ => m₁) := h
        have hfmsp : Lt1 D (f.toFun (Subtype.mk (fun _ => m₁) hmI)).1
            (f.toFun (Subtype.mk sp hspI)).1 :=
          hleftm sp hspI hspJ hc1sp hspm
        have hspS : openInterval D a b sp ∧ Lt1 D sp x₀ ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append sp w) ∧
              Lt1 D w v₀) := hspA
        obtain ⟨-, hspx, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have hspx0 : Lt1 D sp x₀ := hspx
        have hfx : Lt1 D (f.toFun (Subtype.mk sp hspI)).1 v₀ := by
          have eW : w = (f.toFun (Subtype.mk sp hspI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append sp w) = sp := appendLeftAux _ _
            have eR : Power.right (Power.append sp w) = w := appendRightAux _ _
            calc w = Power.right (Power.append sp w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append sp w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk sp hspI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact D.irrefl _ (D.trans hgt (D.trans hfmsp hfx))
      · -- sp = m₁ (coords): then sp ∈ S gives f(m̂) < f(x₀), contra hgt.
        have ept : sp = (fun _ => m₁) := ptEqAux h
        subst ept
        have hspS : openInterval D a b (fun _ => m₁) ∧ Lt1 D (fun _ => m₁) x₀ ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append (fun _ => m₁) w) ∧
              Lt1 D w v₀) := hspA
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
        exact D.irrefl _ (D.trans hgt hwlt)
    -- m₁ is a candidate for x₀.
    set T₀ : Set (Power R 1) := fun y : Power R 1 => openInterval D a b y ∧ Lt1 D y x₀ ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
      (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
        Lt1 D y z → Lt1 D z x₀ →
        (D.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) with hTdef
    have hTmem : M.S 1 T₀ := candDefinable D M f a b x₀ hx₀I
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
        have hzx0 : Lt1 D (f.toFun (Subtype.mk x₀ hx₀I)).1 (f.toFun (Subtype.mk z hzI)).1 := by
          by_contra hne
          rcases D.trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
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
              exact ⟨hzJ, hzx, (f.toFun (Subtype.mk z hzI)).1, hGz, h.left⟩
            have hzUB : D.lt (Power.coord1 z) m₁ ∨ Power.coord1 z = m₁ :=
              hUBm z hzS
            have hzm : Lt1 D (fun _ => m₁) z := hyz
            rcases hzUB with h2 | h2
            · exact D.irrefl _ (D.trans hzm h2)
            · have hzm' : D.lt m₁ (Power.coord1 z) := hzm
              rw [h2] at hzm'
              exact D.irrefl _ hzm'
          · obtain ⟨heq, -, -⟩ := h
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
            have hcon : Lt1 D x₀ x₀ := heqZX ▸ hzx
            exact D.irrefl _ hcon
          · exact False.elim (hne h.left)
        have hgoal : Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1 := by
          rw [eW1]
          exact D.trans hfmX hzx0
        exact hgoal
    -- T₀ is finite: an interval inside would be increasing, contradicting valleys.
    have hTfin : IsFinite1 T₀ := by
      by_contra hne
      have hInf : IsInfinite1 T₀ := hne
      obtain ⟨a', b', hltAB, hsubAB⟩ :=
        Monotonicity_Theorem.infinite_definable_set_contains_interval D M T₀ hTmem hInf
      have hTne : NonEmpty1 T₀ := ⟨_, hmT⟩
      have hJne' : NonEmpty1 (openInterval D a' b') := by
        cases a' with
        | negInf =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val =>
            obtain ⟨y, hym⟩ := D.no_left_endpoint val
            exact ⟨fun _ => y, trivial, hym⟩
          | posInf =>
            obtain ⟨s0, hs0⟩ := hTne
            exact ⟨s0, trivial, trivial⟩
        | finite val =>
          cases b' with
          | negInf => exact False.elim hltAB
          | finite val2 =>
            have hlt2 : D.lt val val2 := hltAB
            obtain ⟨y, hy1, hy2⟩ := D.dense hlt2
            exact ⟨fun _ => y, hy1, hy2⟩
          | posInf =>
            obtain ⟨y, hym⟩ := D.no_right_endpoint val
            exact ⟨fun _ => y, hym, trivial⟩
        | posInf => exact False.elim hltAB
      obtain ⟨p, hp⟩ := hJne'
      obtain ⟨u, v, huv, hsubUV⟩ := finiteSubwindow D hp
      have hinc : forall x (hxI : I x) y (hyI : I y),
          openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
          Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
        intro x hxI y hyI hjx hjy hxy
        have hxT : T₀ x := hsubAB (hsubUV x hjx)
        have hxT' : openInterval D a b x ∧ Lt1 D x x₀ ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append x w) ∧
              Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
            (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
              Lt1 D x z → Lt1 D z x₀ →
              (D.lt (Power.coord1 x) (Power.coord1 z) ∨ Power.coord1 x = Power.coord1 z) →
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x w1) →
              Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) := hxT
        obtain ⟨-, -, -, hxU⟩ := hxT'
        have hyJ : openInterval D a b y := by
          have hyT : T₀ y := hsubAB (hsubUV y hjy)
          have hyT' : openInterval D a b y ∧ Lt1 D y x₀ ∧
              (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                (A := I) (B := B) f.toFun (Power.append y w) ∧
                Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
              (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
                Lt1 D y z → Lt1 D z x₀ →
                (D.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append y w1) →
                Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) := hyT
          exact hyT'.left
        have hyI' : I y := hsubJ _ hyJ
        have hyx0 : Lt1 D y x₀ := by
          have hyTy : T₀ y := hsubAB (hsubUV y hjy)
          have hyT' : openInterval D a b y ∧ Lt1 D y x₀ ∧
              (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                (A := I) (B := B) f.toFun (Power.append y w) ∧
                Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
              (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
                Lt1 D y z → Lt1 D z x₀ →
                (D.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append y w1) →
                Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) := hyTy
          exact hyT'.right.left
        have eLx : Power.left (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) = x :=
          appendLeftAux _ _
        have eRx : Power.right (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) =
            (f.toFun (Subtype.mk x hxI)).1 :=
          appendRightAux _ _
        have hGx : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x ((f.toFun (Subtype.mk x hxI)).1)) :=
          ⟨eLx.symm ▸ hxI, by simp only [eLx, eRx]⟩
        have hleXY : D.lt (Power.coord1 x) (Power.coord1 y) ∨
            Power.coord1 x = Power.coord1 y := Or.inl hxy
        exact hxU y _ hyI' hyJ hxy hyx0 hleXY hGx
      have hsub : forall x, openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
          openInterval D a b x := by
        intro x hx
        have hxT : T₀ x := hsubAB (hsubUV x hx)
        have hxT' : openInterval D a b x ∧ Lt1 D x x₀ ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append x w) ∧
              Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
            (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
              Lt1 D x z → Lt1 D z x₀ →
              (D.lt (Power.coord1 x) (Power.coord1 z) ∨ Power.coord1 x = Power.coord1 z) →
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x w1) →
              Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) := hxT
        exact hxT'.left
      exact Monotonicity_Theorem.incompatible_increasing_above_above D M f
        hsubJ hU huv hsub hinc
    -- Least candidate of T₀.
    obtain ⟨Tlst, hTlst⟩ := hTfin
    have hTne : NonEmpty1 T₀ := ⟨_, hmT⟩
    have hTlstNe : Tlst ≠ [] := by
      intro hEq
      obtain ⟨s0, hs0⟩ := hTne
      have hmem : Power.coord1 s0 ∈ Tlst := (hTlst s0).mp hs0
      rw [hEq] at hmem
      simp at hmem
    obtain ⟨t₁, ht1Mem, ht1Least⟩ :=
      Monotonicity_Theorem.exists_least_of_list D Tlst hTlstNe
    have ht1T : T₀ (fun _ => t₁) := (hTlst _).mpr ht1Mem
    have ht1J : openInterval D a b (fun _ => t₁) := ht1T.left
    have ht1x : Lt1 D (fun _ => t₁) x₀ := ht1T.right.left
    have ht1I : I (fun _ => t₁) := hsubJ _ ht1J
    have ht1ap : openInterval D a ap (fun _ => t₁) := by
      refine ⟨ht1J.left, ?_⟩
      exact hiTrans D ap hx₀mem.right ht1x
    have ht1nL : (fun _ => t₁) ∉ L := hapNoL _ ht1ap
    have ht1I : I (fun _ => t₁) := hsubJ _ ht1J
    set v₁ : Power R 1 := (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 with hv₁def
    set S₁ : Set (Power R 1) := fun y : Power R 1 => openInterval D a b y ∧
      Lt1 D y (fun _ => t₁) ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w v₁) with hS₁def
    -- S(t₁) is nonempty.
    have hNotAll₁ : ¬ forall y w v : Power R 1, I y -> openInterval D a b y -> Lt1 D y (fun _ => t₁) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w) ->
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ => t₁) v) ->
        Lt1 D v w := by
      intro hall
      apply ht1nL
      rw [hLdef]
      exact ⟨ht1J, hall⟩
    obtain ⟨y₂, hy1₂⟩ := Classical.not_forall.mp hNotAll₁
    obtain ⟨w₂, hw1₂⟩ := Classical.not_forall.mp hy1₂
    obtain ⟨v₂, hv1₂⟩ := Classical.not_forall.mp hw1₂
    have hyI₂ : I y₂ :=
      Classical.byContradiction (fun na => hv1₂ (fun a _ _ _ _ => absurd a na))
    have hyJ₂ : openInterval D a b y₂ :=
      Classical.byContradiction (fun na => hv1₂ (fun _ a _ _ _ => absurd a na))
    have hyx₂ : Lt1 D y₂ (fun _ => t₁) :=
      Classical.byContradiction (fun nb => hv1₂ (fun _ _ b _ _ => absurd b nb))
    have hGyw₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y₂ w₂) :=
      Classical.byContradiction (fun nc => hv1₂ (fun _ _ _ c _ => absurd c nc))
    have hGxv₂ : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append (fun _ => t₁) v₂) :=
      Classical.byContradiction (fun nd => hv1₂ (fun _ _ _ _ d => absurd d nd))
    have hne₂ : ¬ Lt1 D v₂ w₂ :=
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
    have hltYX₂ : Lt1 D (f.toFun (Subtype.mk y₂ hyI₂)).1 v₁ := by
      have hne₂' : ¬ Lt1 D v₁ (f.toFun (Subtype.mk y₂ hyI₂)).1 := by
        rw [hv₁def, ← eV₂, ← eW₂]
        exact hne₂
      rcases D.trichotomy (Power.coord1 ((f.toFun (Subtype.mk y₂ hyI₂)).1))
          (Power.coord1 v₁) with h | h | h
      · exact h.left
      · obtain ⟨heq, -, -⟩ := h
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
        have hcon : Lt1 D (fun _ => t₁) (fun _ => t₁) := heqYX ▸ hyx₂
        exact D.irrefl _ hcon
      · exact False.elim (hne₂' h.left)
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
    have hSmem₁ : M.S 1 S₁ := belowPreimageDefinable D M f a b (fun _ => t₁) ht1I
    have hSne₁ : NonEmpty1 S₁ := ⟨y₂, hSwit₂⟩
    have hBnd₁ : BoundedAbove1 D S₁ := by
      refine ⟨t₁, ?_⟩
      intro s hs
      rw [hS₁def] at hs
      obtain ⟨-, hlt, -⟩ := hs
      exact Or.inl hlt
    have hSup₁ := supCompletenessAux D S₁ ((M.ominimal _).mp hSmem₁) hSne₁ hBnd₁
    obtain ⟨m₁', hUBm', hLeastm'⟩ := hSup₁
    obtain ⟨c1t, c2t, hc1Jt, hc2Jt, hc1t, hxt2, hleftt, hrightt⟩ :=
      hU (fun _ => t₁) ht1I ht1J
    have hmc1t : D.lt (Power.coord1 c1t) t₁ := hc1t
    have hc1UB' : IsUpperBound1 D S₁ (Power.coord1 c1t) := by
      intro s hs
      rw [hS₁def] at hs
      obtain ⟨hsJ, hsx, hsW⟩ := hs
      obtain ⟨w, hGw, hwlt⟩ := hsW
      rcases D.trichotomy (Power.coord1 c1t) (Power.coord1 s) with h | h | h
      · obtain ⟨hlt1, -, -⟩ := h
        exfalso
        have hsJab : openInterval D a b s := hsJ
        have hsI : I s := hsubJ _ hsJab
        have hsc1 : Lt1 D c1t s := hlt1
        have hsxt : Lt1 D s (fun _ => t₁) := hsx
        have hwin : Lt1 D v₁ (f.toFun (Subtype.mk s hsI)).1 :=
          hleftt s hsI hsJab hsc1 hsxt
        have hval : Lt1 D (f.toFun (Subtype.mk s hsI)).1 v₁ := by
          have eW : w = (f.toFun (Subtype.mk s hsI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append s w) = s := appendLeftAux _ _
            have eR : Power.right (Power.append s w) = w := appendRightAux _ _
            calc w = Power.right (Power.append s w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append s w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk s hsI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact D.irrefl _ (D.trans hwin hval)
      · obtain ⟨heq, -, -⟩ := h
        exact Or.inr heq.symm
      · obtain ⟨hlt2, -, -⟩ := h
        exact Or.inl hlt2
    have hmUBc1' : D.lt m₁' (Power.coord1 c1t) ∨ m₁' = Power.coord1 c1t :=
      hLeastm' _ hc1UB'
    have hmX' : D.lt m₁' t₁ := by
      rcases hmUBc1' with h | h
      · exact D.trans h hmc1t
      · rw [h]
        exact hmc1t
    have hmJ' : openInterval D a b (fun _ => m₁') := by
      obtain ⟨s0, hs0⟩ := hSne₁
      have hs0' : openInterval D a b s0 ∧ Lt1 D s0 (fun _ => t₁) ∧
          (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
            (A := I) (B := B) f.toFun (Power.append s0 w) ∧
            Lt1 D w v₁) := by
        rw [hS₁def] at hs0
        exact hs0
      obtain ⟨hs0J, hs0x, -⟩ := hs0'
      have hs0le : D.lt (Power.coord1 s0) m₁' ∨ Power.coord1 s0 = m₁' :=
        hUBm' s0 hs0
      have haM : Endpoint.lt D a (Endpoint.finite m₁') := by
        rcases hs0le with h | h
        · exact loTrans D a hs0J.left h
        · rw [← h]
          exact hs0J.left
      have hMb : Endpoint.lt D (Endpoint.finite m₁') b :=
        hiTrans D b ht1J.right hmX'
      exact ⟨haM, hMb⟩
    have hmI' : I (fun _ => m₁') := hsubJ _ hmJ'
    obtain ⟨c1m', c2m', hc1Jm', hc2Jm', hc1m', hxm2', hleftm', hrightm'⟩ :=
      hU (fun _ => m₁') hmI' hmJ'
    have hfmX' : Lt1 D (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 v₁ := by
      by_contra hne
      have hgt : Lt1 D v₁ (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1 := by
        rcases D.trichotomy (Power.coord1 v₁)
            (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁') hmI')).1)) with h | h | h
        · exact h.left
        · obtain ⟨heq, -, -⟩ := h
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
          exact D.irrefl _ hmX'
        · exact False.elim (hne h.left)
      have hmc1' : D.lt (Power.coord1 c1m') m₁' := hc1m'
      obtain ⟨spp, hsppA, hsppt⟩ := notUBofLeast D S₁ m₁' hLeastm' (Power.coord1 c1m') hmc1'
      have hsppm : D.lt (Power.coord1 spp) m₁' ∨ Power.coord1 spp = m₁' :=
        hUBm' spp hsppA
      have hspJ : openInterval D a b spp := by
        have hspA' : openInterval D a b spp ∧ Lt1 D spp (fun _ => t₁) ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append spp w) ∧
              Lt1 D w v₁) := hsppA
        exact hspA'.left
      have hspI : I spp := hsubJ _ hspJ
      rcases hsppm with h | h
      · -- sp < m₁': left window gives f(m̂') < f(sp), but sp ∈ S gives f(sp) < f(t₁) < f(m̂').
        have hc1sp : Lt1 D c1m' spp := hsppt
        -- hsppt : D.lt c1c spc. hc1sp needs Lt1 c1m' spp ≡ D.lt c1c spc ✓ defeq. `exact hsppt`? hsppt : D.lt (coord c1m') (coord spp). Goal Lt1 c1m' spp ≡ same ✓. So `have hc1sp : ... := hsppt`.
        have hspm : Lt1 D spp (fun _ => m₁') := h
        have hfmsp : Lt1 D (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1
            (f.toFun (Subtype.mk spp hspI)).1 :=
          hleftm' spp hspI hspJ hc1sp hspm
        have hspS : openInterval D a b spp ∧ Lt1 D spp (fun _ => t₁) ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append spp w) ∧
              Lt1 D w v₁) := hsppA
        obtain ⟨-, hspx, hspW⟩ := hspS
        obtain ⟨w, hGw, hwlt⟩ := hspW
        have hfx : Lt1 D (f.toFun (Subtype.mk spp hspI)).1 v₁ := by
          have eW : w = (f.toFun (Subtype.mk spp hspI)).1 := by
            obtain ⟨hx0, heq0⟩ := hGw
            have eL : Power.left (Power.append spp w) = spp := appendLeftAux _ _
            have eR : Power.right (Power.append spp w) = w := appendRightAux _ _
            calc w = Power.right (Power.append spp w) := eR.symm
              _ = (f.toFun (Subtype.mk (Power.left (Power.append spp w)) hx0)).1 := heq0
              _ = (f.toFun (Subtype.mk spp hspI)).1 := by simp only [eL]
          rw [← eW]
          exact hwlt
        exact D.irrefl _ (D.trans hgt (D.trans hfmsp hfx))
      · -- sp = m₁' (coords): then sp ∈ S gives f(m̂') < f(t₁), contra hgt.
        have ept : spp = (fun _ => m₁') := ptEqAux h
        subst ept
        have hspS : openInterval D a b (fun _ => m₁') ∧ Lt1 D (fun _ => m₁') (fun _ => t₁) ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append (fun _ => m₁') w) ∧
              Lt1 D w v₁) := hsppA
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
        exact D.irrefl _ (D.trans hgt hwlt)
    -- m₁' is a candidate for t₁.
    set T₁ : Set (Power R 1) := fun y : Power R 1 => openInterval D a b y ∧ Lt1 D y (fun _ => t₁) ∧
      (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (Power.append y w) ∧
        Lt1 D w (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1) ∧
      (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
        Lt1 D y z → Lt1 D z (fun _ => t₁) →
        (D.lt (Power.coord1 y) (Power.coord1 z) ∨ Power.coord1 y = Power.coord1 z) →
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y w1) →
        Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) with hT₁def
    have hT₁mem : M.S 1 T₁ := candDefinable D M f a b (fun _ => t₁) ht1I
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
      have hxmM : Lt1 D (fun _ => m₁') (fun _ => t₁) := hmX'
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
        have hzt1 : Lt1 D (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1
            (f.toFun (Subtype.mk z hzI)).1 := by
          by_contra hne
          rcases D.trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
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
              exact ⟨hzJ, hzx, _, hGz, h.left⟩
            have hzUB : D.lt (Power.coord1 z) m₁' ∨ Power.coord1 z = m₁' :=
              hUBm' z hzS
            have hzm : Lt1 D (fun _ => m₁') z := hyz
            rcases hzUB with h2 | h2
            · exact D.irrefl _ (D.trans hzm h2)
            · have hzm' : D.lt m₁' (Power.coord1 z) := hzm
              rw [h2] at hzm'
              exact D.irrefl _ hzm'
          · obtain ⟨heq, -, -⟩ := h
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
            have hcon : Lt1 D (fun _ => t₁) (fun _ => t₁) := heqZX ▸ hzx
            exact D.irrefl _ hcon
          · exact False.elim (hne h.left)
        have hgoal : Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1 := by
          rw [eW1]
          exact D.trans hfmX' hzt1
        exact hgoal
    -- m₁' lies in T₀ by partition; it is strictly below min T₀: contradiction.
    have hm₁'T₀ : T₀ (fun _ => m₁') := by
      rw [hTdef]
      have hmJ' : openInterval D a b (fun _ => m₁') := by
        obtain ⟨s0, hs0⟩ := hSne₁
        have hs0' : openInterval D a b s0 ∧ Lt1 D s0 (fun _ => t₁) ∧
            (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
              (A := I) (B := B) f.toFun (Power.append s0 w) ∧
              Lt1 D w v₁) := by
          rw [hS₁def] at hs0
          exact hs0
        obtain ⟨hs0J, hs0x, -⟩ := hs0'
        have hs0le : D.lt (Power.coord1 s0) m₁' ∨ Power.coord1 s0 = m₁' :=
          hUBm' s0 hs0
        have haM : Endpoint.lt D a (Endpoint.finite m₁') := by
          rcases hs0le with h | h
          · exact loTrans D a hs0J.left h
          · rw [← h]
            exact hs0J.left
        have hMb : Endpoint.lt D (Endpoint.finite m₁') b :=
          hiTrans D b ht1J.right hmX'
        exact ⟨haM, hMb⟩
      have hxmM' : Lt1 D (fun _ => m₁') x₀ := D.trans hmX' ht1x
      refine ⟨hmJ', ?_, ?_, ?_⟩
      · exact hxmM'
      · -- f(m̂') < f(x₀) via f(t₁).
        have hft1x : Lt1 D (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1
            (f.toFun (Subtype.mk x₀ hx₀I)).1 := by
          have ht1T' : openInterval D a b (fun _ => t₁) ∧ Lt1 D (fun _ => t₁) x₀ ∧
              (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                (A := I) (B := B) f.toFun (Power.append (fun _ => t₁) w) ∧
                Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
              (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
                Lt1 D (fun _ => t₁) z → Lt1 D z x₀ →
                (D.lt (Power.coord1 (fun _ => t₁)) (Power.coord1 z) ∨
                  Power.coord1 (fun _ => t₁) = Power.coord1 z) →
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (Power.append (fun _ => t₁) w1) →
                Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) := ht1T
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
        exact ⟨(f.toFun (Subtype.mk (fun _ => m₁') hmI')).1, hGm, D.trans hfmX' hft1x⟩
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
        have hgoal : Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1 := by
          rw [eW1]
          rcases D.trichotomy (Power.coord1 z) t₁ with h | h | h
          · obtain ⟨hlt1, -, -⟩ := h
            by_contra hne
            rcases D.trichotomy (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
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
                have hltz : Lt1 D ((f.toFun (Subtype.mk z hzI)).1)
                    (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := by
                  have h1 : D.lt (Power.coord1 ((f.toFun (Subtype.mk z hzI)).1))
                      (Power.coord1 ((f.toFun (Subtype.mk (fun _ => m₁') hmI')).1)) := h2.left
                  have h2x : Lt1 D (f.toFun (Subtype.mk (fun _ => m₁') hmI')).1
                      (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1 := hfmX'
                  exact D.trans h1 h2x
                have hzt1 : Lt1 D z (fun _ => t₁) := hlt1
                exact ⟨hzJ, hzt1, _, hGz, hltz⟩
              have hzUB : D.lt (Power.coord1 z) m₁' ∨ Power.coord1 z = m₁' :=
                hUBm' z hzS
              have hzm : Lt1 D (fun _ => m₁') z := hyz
              rcases hzUB with h3 | h3
              · exact D.irrefl _ (D.trans hzm h3)
              · have hzm' : D.lt m₁' (Power.coord1 z) := hzm
                rw [h3] at hzm'
                exact D.irrefl _ hzm'
            · obtain ⟨heq, -, -⟩ := h2
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
              have hcon : Lt1 D (fun _ => m₁') (fun _ => m₁') := heqZM ▸ hyz
              exact D.irrefl _ hcon
            · exact False.elim (hne h2.left)
          · obtain ⟨heq, -, -⟩ := h
            have ept : z = (fun _ => t₁) := ptEqAux heq
            subst ept
            exact hfmX'
          · obtain ⟨hgt, -, -⟩ := h
            have htz : Lt1 D (fun _ => t₁) z := hgt
            have ht1T' : openInterval D a b (fun _ => t₁) ∧ Lt1 D (fun _ => t₁) x₀ ∧
                (exists w : Power R 1, FunctionGraph (R := R) (m := 1) (n := 1)
                  (A := I) (B := B) f.toFun (Power.append (fun _ => t₁) w) ∧
                  Lt1 D w (f.toFun (Subtype.mk x₀ hx₀I)).1) ∧
                (forall z w1 : Power R 1, forall hzI : I z, openInterval D a b z →
                  Lt1 D (fun _ => t₁) z → Lt1 D z x₀ →
                  (D.lt (Power.coord1 (fun _ => t₁)) (Power.coord1 z) ∨
                    Power.coord1 (fun _ => t₁) = Power.coord1 z) →
                  FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                    (Power.append (fun _ => t₁) w1) →
                  Lt1 D w1 (f.toFun (Subtype.mk z hzI)).1) := ht1T
            obtain ⟨-, -, -, ht1U⟩ := ht1T'
            have hleTZ : D.lt (Power.coord1 (fun _ => t₁)) (Power.coord1 z) ∨
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
            have htzv : Lt1 D (f.toFun (Subtype.mk (fun _ => t₁) ht1I)).1
                (f.toFun (Subtype.mk z hzI)).1 :=
              ht1U z _ hzI hzJ htz hzx hleTZ hGt
            exact D.trans hfmX' htzv
        exact hgoal
    -- Contradiction with minimality of t₁.
    have hmemM : Power.coord1 (fun _ => m₁') ∈ Tlst := (hTlst _).mp hm₁'T₀
    have hconLeast : D.lt t₁ (Power.coord1 (fun _ => m₁')) ∨
        t₁ = Power.coord1 (fun _ => m₁') :=
      ht1Least (Power.coord1 (fun _ => m₁')) hmemM
    have hFalse : False := by
      have hltMT : D.lt m₁' t₁ := hmX'
      rcases hconLeast with h | h
      · exact D.irrefl _ (D.trans hltMT h)
      · exact D.irrefl _ (h ▸ hltMT)
    exact False.elim hFalse
  · -- Empty window: take (a,b) itself, vacuously increasing.
    refine ⟨a, b, hlt, hsubJ, ?_⟩
    intro x hxI y hyI hx hy hxy
    exact False.elim (hJne ⟨x, hx⟩)
