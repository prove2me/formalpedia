-- Prove2me | solution 1 for Monotonicity_Theorem.lemma_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T18:02:56.384254+00:00
-- url     : https://prove2.me/submissions/798a7aa1-49d3-45a0-847a-507f44e4186d

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval2
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.SetNotation

open Monotonicity_Theorem
open Classical

-- Auxiliary: append projections.
theorem L1leftAppend {R : Type} {n m : Nat} (x : Power R n) (y : Power R m) :
    Power.left (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem L1rightAppend {R : Type} {n m : Nat} (x : Power R n) (y : Power R m) :
    Power.right (Power.append x y) = y := by
  funext i
  exact Fin.append_right x y i

-- Auxiliary: nondegenerate finite-endpoint intervals are infinite.
theorem L1intervalInfinite {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (u v : R) (huv : LT.lt u v) :
    Set.Infinite (openInterval (Endpoint.finite u) (Endpoint.finite v)) := by
  have hIoo : (Set.Ioo u v).Infinite := Set.Ioo_infinite huv
  have hInj : Set.InjOn (fun r : R => (fun _ => r : Power R 1)) (Set.Ioo u v) := by
    intro r1 _ r2 _ h
    exact congrArg (fun p : Power R 1 => p 0) h
  have hImg := hIoo.image hInj
  apply hImg.mono
  intro x hx
  obtain ⟨r, hrIoo, hrx⟩ := hx
  obtain ⟨hax, hxb⟩ := Set.mem_Ioo.mp hrIoo
  have e : x = (fun _ => r) := hrx.symm
  rw [e]
  exact ⟨hax, hxb⟩

-- Auxiliary: the graph determines values.
theorem L1graphFun {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (x : Power R 1) (hx : I x) (u : Power R 1)
    (hG : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u)) :
    u = (f.toFun ⟨x, hx⟩).1 := by
  obtain ⟨hx', heq⟩ := hG
  have eL : Power.left (Power.append x u) = x := L1leftAppend x u
  have eR : Power.right (Power.append x u) = u := L1rightAppend x u
  have eMk : (⟨Power.left (Power.append x u), hx'⟩ : {x : Power R 1 // I x}) = ⟨x, hx⟩ :=
    Subtype.ext eL
  rw [eMk, eR] at heq
  exact heq

-- Auxiliary: the graph contains all true values.
theorem L1graphMem {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (y : Power R 1) (hy : I y) :
    FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
      (Power.append y (f.toFun ⟨y, hy⟩).1) := by
  have eL : Power.left (Power.append y (f.toFun ⟨y, hy⟩).1) = y := L1leftAppend _ _
  have eR : Power.right (Power.append y (f.toFun ⟨y, hy⟩).1) = (f.toFun ⟨y, hy⟩).1 :=
    L1rightAppend _ _
  have hx : I (Power.left (Power.append y (f.toFun ⟨y, hy⟩).1)) := by
    rw [L1leftAppend]
    exact hy
  have eMk : (⟨Power.left (Power.append y (f.toFun ⟨y, hy⟩).1), hx⟩ : {x : Power R 1 // I x})
      = ⟨y, hy⟩ := Subtype.ext eL
  refine ⟨hx, ?_⟩
  rw [eR, eMk]

-- Auxiliary: right-coordinate projection.
theorem L1rightCoord {R : Type} (z : Power R 2) : (Power.right (n := 1) (m := 1) z) 0 = z 1 := by
  show z (Fin.natAdd 1 (0 : Fin 1)) = z 1
  congr 1

-- Fiber meet over a working interval: values taken at x with witness u
-- whose coordinate matches v. Stated in S-native form (no bridges needed).
theorem L1fiberMeetDef {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (J : Set (Power R 1)) (hJ : M.S 1 J) (v : Power R 1) :
    M.S 1 (fun x : Power R 1 => I x /\ J x /\ ∃ u : Power R 1,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u) /\
        (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = v 0) := by
  have hP : M.S 1 (pointSet (v 0)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point _)
  have hPr : M.S 2 (fun z : Power R 2 => (Power.right (n := 1) (m := 1) z) 0 = v 0) := by
    have h := M.reindex_mem (fun _ : Fin 1 => (1 : Fin 2)) hP
    have e : (fun z : Power R 2 => pointSet (v 0) (fun _ => z 1)) =
        (fun z : Power R 2 => (Power.right (n := 1) (m := 1) z) 0 = v 0) := by
      simp only [pointSet, L1rightCoord]
    rw [e] at h
    exact h
  have hH : M.S 2 (fun z : Power R 2 =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun z /\
        (Power.right (n := 1) (m := 1) z) 0 = v 0) :=
    M.inter_mem f.graph_mem hPr
  have hE : M.S 1 (fun x : Power R 1 => ∃ u : Power R 1,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u) /\
        (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = v 0) :=
    M.existsLast_mem (n := 1) (m := 1) hH
  exact M.inter_mem f.domain_mem (M.inter_mem hJ hE)

-- L1deleteCoord1.
theorem L1deleteCoord1 {R : Type} (p : Power R 2) : Power.deleteCoord (n := 1) (1 : Fin 2) p = (fun _ => p 0) := by
  funext i
  have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
  have hi : i = (0 : Fin 1) := Fin.ext hi0
  rw [hi]
  show p (Fin.succAbove (1 : Fin 2) (0 : Fin 1)) = p 0
  congr 1

-- Index maps for the J3 matrix (named once, referenced on both sides).
def L1sigX : Fin 1 → Fin 4 := fun _ => 0
def L1sigY : Fin 1 → Fin 4 := fun _ => 1
def L1sigYU : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then 1 else 2
def L1sigXW : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then 0 else 3
def L1sigLT : Fin 2 → Fin 4 := fun j => if _ : j.val = 0 then 0 else 1

-- E4 matrix and its definability.
theorem L1E4def {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (J : Set (Power R 1)) (hJ : M.S 1 J) :
    M.S 4 (fun w : Power R 4 =>
      J (fun i : Fin 1 => w (L1sigX i)) /\
      J (fun i : Fin 1 => w (L1sigY i)) /\
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin 2 => w (L1sigYU j)) /\
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin 2 => w (L1sigXW j)) /\
      w 2 = w 3 /\
      ¬ ((fun i : Fin 2 => w (L1sigLT i)) 0 < (fun i : Fin 2 => w (L1sigLT i)) 1 \/
        (fun _ : Fin 1 => w 0) = (fun _ : Fin 1 => w 1))) := by
  have hJx := M.reindex_mem L1sigX hJ
  have hJy := M.reindex_mem L1sigY hJ
  have hGyu := M.reindex_mem L1sigYU f.graph_mem
  have hGxw := M.reindex_mem L1sigXW f.graph_mem
  have hEq : M.S 4 (fun w : Power R 4 => w 2 = w 3) :=
    M.diagonal_mem (2 : Fin 4) (3 : Fin 4) (by decide)
  have hLt : M.S 4 (fun w : Power R 4 =>
      (fun i : Fin 2 => w (L1sigLT i)) 0 < (fun i : Fin 2 => w (L1sigLT i)) 1) :=
    M.reindex_mem L1sigLT M.lt_mem
  have hEq1 : M.S 4 (fun w : Power R 4 => (fun _ : Fin 1 => w 0) = (fun _ : Fin 1 => w 1)) := by
    have h := M.diagonal_mem (0 : Fin 4) (1 : Fin 4) (by decide)
    have e : (fun w : Power R 4 => w 0 = w 1) =
        (fun w : Power R 4 => (fun _ : Fin 1 => w 0) = (fun _ : Fin 1 => w 1)) := by
      funext w
      apply propext
      constructor
      · intro h0
        funext i
        exact h0
      · intro h1
        exact congrFun h1 0
    rw [← e]
    exact h
  exact M.inter_mem hJx (M.inter_mem hJy (M.inter_mem hGyu (M.inter_mem hGxw
    (M.inter_mem hEq (M.compl_mem (M.union_mem hLt hEq1))))))

-- Bridge: fiber-meet membership pins the value.
theorem L1fiberVal {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (v : Power R 1)
    (x : Power R 1) (hxI : I x) (u : Power R 1)
    (hGu : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u))
    (hco : (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = v 0) :
    (f.toFun ⟨x, hxI⟩).1 = v := by
  have hu : u = (f.toFun ⟨x, hxI⟩).1 := L1graphFun M f x hxI u hGu
  have eR : Power.right (n := 1) (m := 1) (Power.append x u) = u := L1rightAppend x u
  rw [eR] at hco
  rw [hu] at hco
  funext i
  have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
  have hi : i = (0 : Fin 1) := Fin.ext hi0
  rw [hi]
  exact hco


-- Append Bridges for reindexed pairs.
theorem L1appendYU {R : Type} (w4 : Power R 4) :
    (fun j : Fin 2 => w4 (L1sigYU j)) =
      Power.append (fun _ : Fin 1 => w4 1) (fun _ : Fin 1 => w4 2) := by
  funext j
  fin_cases j <;> rfl

theorem L1appendXW {R : Type} (w4 : Power R 4) :
    (fun j : Fin 2 => w4 (L1sigXW j)) =
      Power.append (fun _ : Fin 1 => w4 0) (fun _ : Fin 1 => w4 3) := by
  funext j
  fin_cases j <;> rfl

-- Append-coordinate computations (all literal indices, check by rfl).
theorem L1app000 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 0 = x 0 := rfl

theorem L1app001 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 1 = y 0 := rfl

theorem L1app002 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 2 = u 0 := rfl

theorem L1app003 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 3 = w 0 := rfl


-- Append-coordinate computations for the peel nest.
theorem L1appZ0 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 0 = z 0 := rfl

theorem L1appZ1 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 1 = z 1 := rfl

theorem L1appZ2 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 2 = u 0 := rfl

theorem L1appZ3 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 3 = w 0 := rfl



-- Least-element locus, stated once and referenced by name.
def L1J3set {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (J : Set (Power R 1)) : Set (Power R 1) :=
  fun x : Power R 1 => J x /\ ¬ ∃ z : Power R 2,
    (fun z : Power R 2 => ∃ u : Power R 1,
      (fun t : Power R 3 => ∃ w : Power R 1,
        (fun w4 : Power R 4 =>
          J (fun i : Fin 1 => w4 (L1sigX i)) /\
          J (fun i : Fin 1 => w4 (L1sigY i)) /\
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin 2 => w4 (L1sigYU j)) /\
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin 2 => w4 (L1sigXW j)) /\
          w4 2 = w4 3 /\
          ¬ (((fun i : Fin 2 => w4 (L1sigLT i)) 0 < (fun i : Fin 2 => w4 (L1sigLT i)) 1) \/
            (fun _ : Fin 1 => w4 0) = (fun _ : Fin 1 => w4 1)))
        (Power.append t w))
      (Power.append z u)) z /\
    Power.deleteCoord (n := 1) (1 : Fin 2) z = x



theorem Monotonicity_Theorem.exists_least_of_list {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (L : List R) (hNe : L ≠ []) :
    ∃ m : R, m ∈ L ∧ ∀ r : R, r ∈ L → (LT.lt m r ∨ m = r) := by
  induction L with
  | nil => contradiction
  | cons x B ih =>
    by_cases hB : B = []
    · subst hB
      refine ⟨x, List.Mem.head _, fun r hr => ?_⟩
      cases hr with
      | head => exact Or.inr rfl
      | tail _ h => cases h
    · have hBne : B ≠ [] := hB
      obtain ⟨mB, hmBin, hmBlower⟩ := ih hBne
      by_cases hlt : LT.lt x mB
      · refine ⟨x, List.Mem.head _, fun r hr => ?_⟩
        cases hr with
        | head => exact Or.inr rfl
        | tail _ hrB =>
          cases hmBlower r hrB with
          | inl h => exact Or.inl (lt_trans hlt h)
          | inr heq => exact Or.inl (by rw [← heq]; exact hlt)
      · refine ⟨mB, List.Mem.tail _ hmBin, fun r hr => ?_⟩
        cases hr with
        | head =>
          rcases lt_trichotomy x mB with h | heq | h
          · exact absurd h hlt
          · exact Or.inr heq.symm
          · exact Or.inl h
        | tail _ hrB => exact hmBlower r hrB


-- Triple-nest append coordinates (literal indices, check by rfl).
theorem L1appW0 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 0 = z 0 := rfl

theorem L1appW1 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 1 = z 1 := rfl

theorem L1appW2 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 2 = u 0 := rfl

theorem L1appW3 {R : Type} (z : Power R 2) (u w : Power R 1) :
    (Power.append (Power.append z u) w) 3 = w 0 := rfl

-- Pair-nest append coordinates (for building witnesses).
theorem L1appP0 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 0 = x 0 := rfl

theorem L1appP1 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 1 = y 0 := rfl

theorem L1appP2 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 2 = u 0 := rfl

theorem L1appP3 {R : Type} (x y u w : Power R 1) :
    (Power.append (Power.append (Power.append x y) u) w) 3 = w 0 := rfl


theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (M : OMinimalStructure R)
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (hI : Set.Infinite I) :
    ∃ a b : Endpoint R, Endpoint.lt a b ∧
      (openInterval a b).Subset I ∧
      ((∀ x (hxI : I x), openInterval a b x → ∀ y (hyI : I y), openInterval a b y →
          f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI)) ∨
       (∀ x (hxI : I x), openInterval a b x → ∀ y (hyI : I y), openInterval a b y →
          f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI) → x = y)) := by
  obtain ⟨a0, b0, hlt0, hsub0⟩ :=
    Monotonicity_Theorem.infinite_definable_set_contains_interval2 M I f.domain_mem hI
  have hJ₀ : M.S 1 (openInterval a0 b0) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hJinf : Set.Infinite (openInterval a0 b0) := by
    cases a0 with
    | negInf =>
        cases b0 with
        | negInf => intro hFin; exact hlt0
        | finite v =>
            obtain ⟨u, huv⟩ := exists_lt v
            have hsub : openInterval (Endpoint.finite u) (Endpoint.finite v) ⊆
                openInterval Endpoint.negInf (Endpoint.finite v) := by
              intro x hx
              exact ⟨trivial, hx.2⟩
            intro hFin
            exact (L1intervalInfinite u v huv) (hFin.subset hsub)
        | posInf =>
            obtain ⟨p, hp⟩ := hI.nonempty
            obtain ⟨u, hu⟩ := exists_lt (p 0)
            obtain ⟨v, hv⟩ := exists_gt (p 0)
            have huv : LT.lt u v := lt_trans hu hv
            have hsub : openInterval (Endpoint.finite u) (Endpoint.finite v) ⊆
                openInterval Endpoint.negInf Endpoint.posInf := by
              intro x hx
              exact ⟨trivial, trivial⟩
            intro hFin
            exact (L1intervalInfinite u v huv) (hFin.subset hsub)
    | finite u =>
        cases b0 with
        | negInf => intro hFin; exact hlt0
        | finite v =>
            by_cases huv : LT.lt u v
            · exact L1intervalInfinite u v huv
            · intro hFin
              exact huv hlt0
        | posInf =>
            obtain ⟨v, hv⟩ := exists_gt u
            have hsub : openInterval (Endpoint.finite u) (Endpoint.finite v) ⊆
                openInterval (Endpoint.finite u) Endpoint.posInf := by
              intro x hx
              exact ⟨hx.1, trivial⟩
            intro hFin
            exact (L1intervalInfinite u v hv) (hFin.subset hsub)
    | posInf =>
        cases b0 with
        | negInf => intro hFin; exact hlt0
        | finite v => intro hFin; exact hlt0
        | posInf => intro hFin; exact hlt0
  -- Fiber meets are definable.
  have hFdef : ∀ v : Power R 1, M.S 1 (fun x : Power R 1 => I x /\ openInterval a0 b0 x /\
      ∃ u : Power R 1,
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u) /\
          (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = v 0) := by
    intro v
    exact L1fiberMeetDef M f _ hJ₀ v
  -- Fiber membership pins the value.
  have hFval : ∀ (v : Power R 1) (x : Power R 1) (hxI : I x) (u : Power R 1)
      (hGu : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u))
      (hco : (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = v 0),
      (f.toFun ⟨x, hxI⟩).1 = v := by
    intro v x hxI u hGu hco
    have hu : u = (f.toFun ⟨x, hxI⟩).1 := L1graphFun M f x hxI u hGu
    have eR : Power.right (n := 1) (m := 1) (Power.append x u) = u := L1rightAppend x u
    rw [eR] at hco
    rw [hu] at hco
    funext i
    have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext hi0
    rw [hi]
    exact hco
  -- Split on infinite fibers.
  by_cases h : ∃ v : Power R 1, Set.Infinite (fun x : Power R 1 => I x /\ openInterval a0 b0 x /\
      ∃ u : Power R 1,
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u) /\
          (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = v 0)
  · obtain ⟨v, hvinf⟩ := h
    obtain ⟨a, b, hlt, hsub⟩ :=
      Monotonicity_Theorem.infinite_definable_set_contains_interval2 M _ (hFdef v) hvinf
    refine ⟨a, b, hlt, ?_, Or.inl ?_⟩
    · intro x hx
      have hxF := hsub hx
      obtain ⟨hxI, -, -⟩ := hxF
      exact hxI
    · intro x hxI hxJ y hyI hyJ
      obtain ⟨-, -, u, hGu, hco⟩ := hsub hxJ
      obtain ⟨-, -, w, hGw, hco2⟩ := hsub hyJ
      have hxv : (f.toFun ⟨x, hxI⟩).1 = v := hFval v x hxI u hGu hco
      have hyv : (f.toFun ⟨y, hyI⟩).1 = v := hFval v y hyI w hGw hco2
      apply Subtype.ext
      rw [hxv, hyv]
  · -- All meets finite: least-element locus.
    have hfin : ∀ v : Power R 1, Set.Finite (fun x : Power R 1 => I x /\ openInterval a0 b0 x /\
        ∃ u : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun (Power.append x u) /\
            (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = v 0) := by
      intro v
      by_contra hcon
      exact h ⟨v, hcon⟩
    have hE4 := L1E4def M f (openInterval a0 b0) hJ₀
    have h3 := M.existsLast_mem (n := 3) (m := 1) hE4
    have hE2 := M.existsLast_mem (n := 2) (m := 1) h3
    have hpi := M.project_mem (n := 1) (1 : Fin 2) hE2
    have hJ3 : M.S 1 (L1J3set M f (openInterval a0 b0)) := by
      unfold L1J3set
      exact M.inter_mem hJ₀ (M.compl_mem hpi)

    -- D1: minimality puts points in J3.
    have hJ3mem : ∀ m : Power R 1, openInterval a0 b0 m →
        (∀ y : Power R 1, openInterval a0 b0 y →
          (∃ u w : Power R 1,
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y u) /\
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append m w) /\
            u 0 = w 0) →
          (Lt1 m y ∨ m 0 = y 0)) →
        m ∈ L1J3set M f (openInterval a0 b0) := by
      intro m hmJ hmin
      refine ⟨hmJ, ?_⟩
      intro hcon
      obtain ⟨z, hz⟩ := hcon
      obtain ⟨hzE, hzD⟩ := hz
      obtain ⟨u, hz3⟩ := hzE
      obtain ⟨w, hE4w⟩ := hz3
      obtain ⟨hJzx, hJzy, hGyu, hGxw, hEq, hNle⟩ := hE4w
      -- Coordinate computations.
      have c0 : (Power.append (Power.append z u) w) 0 = z 0 := L1appZ0 z u w
      have c1 : (Power.append (Power.append z u) w) 1 = z 1 := L1appZ1 z u w
      have c2 : (Power.append (Power.append z u) w) 2 = u 0 := L1appZ2 z u w
      have c3 : (Power.append (Power.append z u) w) 3 = w 0 := L1appZ3 z u w
      -- m as a constant tuple.
      have eM0 : m 0 = (Power.append (Power.append z u) w) 0 := by
        have hD := L1deleteCoord1 z
        rw [hzD] at hD
        calc m 0 = (fun _ : Fin 1 => z 0) 0 := congrFun hD 0
          _ = z 0 := rfl
          _ = (Power.append (Power.append z u) w) 0 := c0.symm
      have eM : m = (fun _ : Fin 1 => (Power.append (Power.append z u) w) 0) := by
        funext i
        have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
        have hi : i = (0 : Fin 1) := Fin.ext hi0
        rw [hi]
        exact eM0
      have eM : m = (fun _ : Fin 1 => (Power.append (Power.append z u) w) 0) := by
        funext i
        have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
        have hi : i = (0 : Fin 1) := Fin.ext hi0
        rw [hi]
        exact eM0
      have hyJ : openInterval a0 b0 (fun _ : Fin 1 => (Power.append (Power.append z u) w) 1) := hJzy
      rw [L1appendYU] at hGyu
      rw [L1appendXW] at hGxw
      have hGyu2 : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append (fun _ : Fin 1 => (Power.append (Power.append z u) w) 1)
            (fun _ : Fin 1 => (Power.append (Power.append z u) w) 2)) := hGyu
      have hGxw2 : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append m (fun _ : Fin 1 => (Power.append (Power.append z u) w) 3)) := by
        rw [eM]
        exact hGxw
      have hco : (fun _ : Fin 1 => (Power.append (Power.append z u) w) 2) 0 =
          (fun _ : Fin 1 => (Power.append (Power.append z u) w) 3) 0 := hEq
      have hconc := hmin (fun _ : Fin 1 => (Power.append (Power.append z u) w) 1) hyJ
        ⟨(fun _ : Fin 1 => (Power.append (Power.append z u) w) 2),
          (fun _ : Fin 1 => (Power.append (Power.append z u) w) 3), hGyu2, hGxw2, hco⟩
      have eY : (fun _ : Fin 1 => (Power.append (Power.append z u) w) 1) 0 =
          (Power.append (Power.append z u) w) 1 := rfl
      cases hconc with
      | inl hlt =>
          apply hNle
          left
          show (Power.append (Power.append z u) w) 0 < (Power.append (Power.append z u) w) 1
          rw [← eM0, ← eY]
          exact hlt
          | inr heq =>
              apply hNle
              right
              funext i
              show (Power.append (Power.append z u) w) 0 =
                (Power.append (Power.append z u) w) 1
              have e1 : z 0 = m 0 := (L1appZ0 z u w).symm.trans eM0.symm
              exact (L1appZ0 z u w).trans (e1.trans (heq.trans eY))

    -- Least sharing points.
    have hLeast : ∀ x : Power R 1, openInterval a0 b0 x →
        ∃ m : Power R 1, openInterval a0 b0 m ∧
          (∃ u w : Power R 1,
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append x u) /\
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append m w) /\
            u 0 = w 0) ∧
          ∀ y : Power R 1, openInterval a0 b0 y →
            (∃ u w : Power R 1,
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append y u) /\
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append m w) /\
              u 0 = w 0) →
            (Lt1 m y ∨ m 0 = y 0) := by
      intro x hxJ
      have hxI : I x := hsub0 hxJ
      -- S_x and its finiteness.
      have hxI : I x := hsub0 hxJ
      have hxSx : (fun y : Power R 1 => openInterval a0 b0 y ∧ ∃ u w : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y u) /\
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x w) /\
          u 0 = w 0) x := by
        refine ⟨hxJ, ?_⟩
        exact ⟨(f.toFun ⟨x, hxI⟩).1, (f.toFun ⟨x, hxI⟩).1,
          L1graphMem M f x hxI, L1graphMem M f x hxI, rfl⟩
      have hSsub : Set.Subset (fun y : Power R 1 => openInterval a0 b0 y ∧ ∃ u w : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y u) /\
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x w) /\
          u 0 = w 0)
          (fun y : Power R 1 => I y ∧ openInterval a0 b0 y ∧ ∃ u : Power R 1,
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y u) /\
            (Power.right (n := 1) (m := 1) (Power.append y u)) 0 = ((f.toFun ⟨x, hxI⟩).1) 0) := by
        intro y hy
        obtain ⟨hyJ, u, w, hGu, hGw, hco⟩ := hy
        have hyI : I y := hsub0 hyJ
        have hw : w = (f.toFun ⟨x, hxI⟩).1 := L1graphFun M f x hxI w hGw
        refine ⟨hyI, hyJ, u, hGu, ?_⟩
        have eR : Power.right (n := 1) (m := 1) (Power.append y u) = u := L1rightAppend y u
        rw [eR, hco]
        exact congrArg (fun t => t 0) hw
      have hSfin : Set.Finite (fun y : Power R 1 => openInterval a0 b0 y ∧ ∃ u w : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y u) /\
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x w) /\
          u 0 = w 0) :=
        Set.Finite.subset (hfin ((f.toFun ⟨x, hxI⟩).1)) (fun y hy => hSsub hy)
      have hLne : (((hSfin.toFinset).toList.map Power.coord1)) ≠ [] := by
        have hmem : Power.coord1 x ∈ (((hSfin.toFinset).toList.map Power.coord1)) :=
          List.mem_map.mpr ⟨x, Finset.mem_toList.mpr ((Set.Finite.mem_toFinset hSfin).mpr hxSx), rfl⟩
        exact List.ne_nil_of_mem hmem
      obtain ⟨c0, hc0mem, hc0min⟩ :=
        Monotonicity_Theorem.exists_least_of_list (((hSfin.toFinset).toList.map Power.coord1)) hLne
      obtain ⟨m, hmL, hmeq⟩ := List.mem_map.mp hc0mem
      have hmT : m ∈ hSfin.toFinset := Finset.mem_toList.mp hmL
      have hmSx := (Set.Finite.mem_toFinset hSfin).mp hmT
      obtain ⟨hmJ, hmV⟩ := hmSx
      refine ⟨m, hmJ, ?_, ?_⟩
      · obtain ⟨u, w, hGu, hGw, hco⟩ := hmV
        exact ⟨w, u, hGw, hGu, hco.symm⟩
      · intro y hyJ hfib
        obtain ⟨u1, w1, hGu1, hGw1, hco1⟩ := hfib
        obtain ⟨u2, w2, hGu2, hGw2, hco2⟩ := hmV
        have hyI : I y := hsub0 hyJ
        have hmI2 : I m := hsub0 hmJ
        have e1 : (f.toFun ⟨y, hyI⟩).1 = (f.toFun ⟨m, hmI2⟩).1 := by
          have g1 : u1 = (f.toFun ⟨y, hyI⟩).1 := L1graphFun M f y hyI u1 hGu1
          have g2 : w1 = (f.toFun ⟨m, hmI2⟩).1 := L1graphFun M f m hmI2 w1 hGw1
          have c1 : (f.toFun ⟨y, hyI⟩).1 0 = (f.toFun ⟨m, hmI2⟩).1 0 := by
            have a1 : u1 0 = (f.toFun ⟨y, hyI⟩).1 0 := congrArg (fun t => t 0) g1
            have a2 : w1 0 = (f.toFun ⟨m, hmI2⟩).1 0 := congrArg (fun t => t 0) g2
            rw [← a1, hco1]
            exact a2
          funext i
          have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
          have hi : i = (0 : Fin 1) := Fin.ext hi0
          rw [hi]
          exact c1
        have e2 : (f.toFun ⟨m, hmI2⟩).1 = (f.toFun ⟨x, hxI⟩).1 := by
          have g1 : u2 = (f.toFun ⟨m, hmI2⟩).1 := L1graphFun M f m hmI2 u2 hGu2
          have g2 : w2 = (f.toFun ⟨x, hxI⟩).1 := L1graphFun M f x hxI w2 hGw2
          have c1 : (f.toFun ⟨m, hmI2⟩).1 0 = (f.toFun ⟨x, hxI⟩).1 0 := by
            have a1 : u2 0 = (f.toFun ⟨m, hmI2⟩).1 0 := congrArg (fun t => t 0) g1
            have a2 : w2 0 = (f.toFun ⟨x, hxI⟩).1 0 := congrArg (fun t => t 0) g2
            rw [← a1, hco2]
            exact a2
          funext i
          have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
          have hi : i = (0 : Fin 1) := Fin.ext hi0
          rw [hi]
          exact c1
        have eyx : (f.toFun ⟨y, hyI⟩).1 = (f.toFun ⟨x, hxI⟩).1 := e1.trans e2
        have hySx : (fun y : Power R 1 => openInterval a0 b0 y ∧ ∃ u w : Power R 1,
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y u) /\
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append x w) /\
            u 0 = w 0) y :=
          ⟨hyJ, (f.toFun ⟨y, hyI⟩).1, (f.toFun ⟨x, hxI⟩).1,
            L1graphMem M f y hyI, L1graphMem M f x hxI,
            congrArg (fun t => t 0) eyx⟩
        have hyL : Power.coord1 y ∈ (((hSfin.toFinset).toList.map Power.coord1)) :=
          List.mem_map.mpr ⟨y, Finset.mem_toList.mpr ((Set.Finite.mem_toFinset hSfin).mpr hySx), rfl⟩
        have hle := hc0min _ hyL
        rw [← hmeq] at hle
        cases hle with
        | inl hlt =>
            left
            show Power.coord1 m < Power.coord1 y
            exact hlt
        | inr heq =>
            right
            show m 0 = y 0
            exact heq

    -- J3 is infinite (least elements cover J0).
    have hJinf3 : Set.Infinite (L1J3set M f (openInterval a0 b0)) := by
      by_contra hcon
      have hJ3fin : Set.Finite (L1J3set M f (openInterval a0 b0)) := by
        by_contra hc
        exact hcon hc
      have hcover : ∀ x : Power R 1, openInterval a0 b0 x →
          ∃ m : Power R 1, m ∈ hJ3fin.toFinset ∧
            (∃ u w : Power R 1,
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x u) /\
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append m w) /\
              u 0 = w 0) := by
        intro x hxJ
        obtain ⟨m, hmJ, hval, hmin⟩ := hLeast x hxJ
        have hm3 : m ∈ L1J3set M f (openInterval a0 b0) := hJ3mem m hmJ hmin
        refine ⟨m, (Set.Finite.mem_toFinset hJ3fin).mpr hm3, hval⟩
      have hUfin : Set.Finite (⋃ m ∈ (↑hJ3fin.toFinset : Set (Power R 1)),
          (fun x : Power R 1 => openInterval a0 b0 x ∧ ∃ u w : Power R 1,
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append x u) /\
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append m w) /\
            u 0 = w 0)) := by
        apply Set.Finite.biUnion (Finset.finite_toSet _)
        intro m hm
        have hmT : m ∈ hJ3fin.toFinset := Finset.mem_coe.mp hm
        have hm3 := (Set.Finite.mem_toFinset hJ3fin).mp hmT
        obtain ⟨hmJ, -⟩ := hm3
        have hmI : I m := hsub0 hmJ
        have hsubm : Set.Subset (fun x : Power R 1 => openInterval a0 b0 x ∧ ∃ u w : Power R 1,
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append x u) /\
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append m w) /\
            u 0 = w 0)
            (fun x : Power R 1 => I x ∧ openInterval a0 b0 x ∧ ∃ u : Power R 1,
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x u) /\
              (Power.right (n := 1) (m := 1) (Power.append x u)) 0 = ((f.toFun ⟨m, hmI⟩).1) 0) := by
          intro y hy
          obtain ⟨hyJ, u, w, hGu, hGw, hco⟩ := hy
          have hyI : I y := hsub0 hyJ
          have hu : u = (f.toFun ⟨y, hyI⟩).1 := L1graphFun M f y hyI u hGu
          have hw : w = (f.toFun ⟨m, hmI⟩).1 := L1graphFun M f m hmI w hGw
          refine ⟨hyI, hyJ, u, hGu, ?_⟩
          have eR : Power.right (n := 1) (m := 1) (Power.append y u) = u := L1rightAppend y u
          rw [eR, hco]
          exact congrArg (fun t => t 0) hw
        exact Set.Finite.subset (hfin ((f.toFun ⟨m, hmI⟩).1)) (fun y hy => hsubm hy)
      have hsubU : Set.Subset (openInterval a0 b0)
          (⋃ m ∈ (↑hJ3fin.toFinset : Set (Power R 1)),
            (fun x : Power R 1 => openInterval a0 b0 x ∧ ∃ u w : Power R 1,
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append x u) /\
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (Power.append m w) /\
              u 0 = w 0)) := by
        intro x hxJ
        obtain ⟨m, hmT, hval⟩ := hcover x hxJ
        exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmT, hxJ, hval⟩⟩
      have hJ0fin : Set.Finite (openInterval a0 b0) := Set.Finite.subset hUfin (fun y hy => hsubU hy)
      exact hJinf hJ0fin

    -- Characterization: J3 points are fiber-least.
    have hChar : ∀ x : Power R 1, x ∈ L1J3set M f (openInterval a0 b0) →
        ∀ y : Power R 1, openInterval a0 b0 y →
          (∃ u w : Power R 1,
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append y u) /\
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (Power.append x w) /\
            u 0 = w 0) →
          (Lt1 x y ∨ x 0 = y 0) := by
      intro x hx3 y hyJ hfib
      obtain ⟨hxJ, hxN⟩ := hx3
      obtain ⟨u0, w0, hGu0, hGw0, hco0⟩ := hfib
      by_contra hle
      apply hxN
      refine ⟨Power.append x y, ?_, ?_⟩
      · refine ⟨u0, ?_⟩
        refine ⟨w0, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- Jx.
          have eX : (fun i : Fin 1 => (Power.append (Power.append (Power.append x y) u0) w0) (L1sigX i)) = x := by
            funext i
            have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
            have hi : i = (0 : Fin 1) := Fin.ext hi0
            rw [hi]
            show (Power.append (Power.append (Power.append x y) u0) w0) 0 = x 0
            exact L1appP0 x y u0 w0
          rw [eX]
          exact hxJ
        · -- Jy.
          have eY : (fun i : Fin 1 => (Power.append (Power.append (Power.append x y) u0) w0) (L1sigY i)) = y := by
            funext i
            have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
            have hi : i = (0 : Fin 1) := Fin.ext hi0
            rw [hi]
            show (Power.append (Power.append (Power.append x y) u0) w0) 1 = y 0
            exact L1appP1 x y u0 w0
          rw [eY]
          exact hyJ
        · -- Gyu.
          rw [L1appendYU]
          have eY1 : (fun _ : Fin 1 => (Power.append (Power.append (Power.append x y) u0) w0) 1) = y := by
            funext i
            have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
            have hi : i = (0 : Fin 1) := Fin.ext hi0
            rw [hi]
            show (Power.append (Power.append (Power.append x y) u0) w0) 1 = y 0
            exact L1appP1 x y u0 w0
          have eU2 : (fun _ : Fin 1 => (Power.append (Power.append (Power.append x y) u0) w0) 2) = u0 := by
            funext i
            have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
            have hi : i = (0 : Fin 1) := Fin.ext hi0
            rw [hi]
            show (Power.append (Power.append (Power.append x y) u0) w0) 2 = u0 0
            exact L1appP2 x y u0 w0
          rw [eY1, eU2]
          exact hGu0
        · -- Gxw.
          rw [L1appendXW]
          have eX0 : (fun _ : Fin 1 => (Power.append (Power.append (Power.append x y) u0) w0) 0) = x := by
            funext i
            have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
            have hi : i = (0 : Fin 1) := Fin.ext hi0
            rw [hi]
            show (Power.append (Power.append (Power.append x y) u0) w0) 0 = x 0
            exact L1appP0 x y u0 w0
          have eW3 : (fun _ : Fin 1 => (Power.append (Power.append (Power.append x y) u0) w0) 3) = w0 := by
            funext i
            have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
            have hi : i = (0 : Fin 1) := Fin.ext hi0
            rw [hi]
            show (Power.append (Power.append (Power.append x y) u0) w0) 3 = w0 0
            exact L1appP3 x y u0 w0
          rw [eX0, eW3]
          exact hGw0
        · -- diagonal.
          rw [L1appP2, L1appP3]
          exact hco0
        · -- not-le.
          intro hcon
          cases hcon with
          | inl hlt =>
              apply hle
              left
              show (Power.append (Power.append (Power.append x y) u0) w0) 0 <
                (Power.append (Power.append (Power.append x y) u0) w0) 1
              rw [L1appP0, L1appP1]
              show Power.coord1 x < Power.coord1 y
              exact hlt
          | inr heq =>
              apply hle
              right
              have hW : (Power.append (Power.append (Power.append x y) u0) w0) 0 =
                  (Power.append (Power.append (Power.append x y) u0) w0) 1 :=
                congrFun heq 0
              rw [L1appP0, L1appP1] at hW
              exact hW
      · -- deleteCoord condition.
        have eD : Power.deleteCoord (n := 1) (1 : Fin 2) (Power.append x y) = x := by
          funext i
          have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
          have hi : i = (0 : Fin 1) := Fin.ext hi0
          rw [hi]
          have h1 : (Power.deleteCoord (n := 1) (1 : Fin 2) (Power.append x y)) 0 =
              (Power.append x y) 0 := congrFun (L1deleteCoord1 (Power.append x y)) 0
          rw [h1]
          rfl
        exact eD
    -- Interval inside J3.
    obtain ⟨a, b, hlt, hsub⟩ :=
      Monotonicity_Theorem.infinite_definable_set_contains_interval2 M _ hJ3 hJinf3
    refine ⟨a, b, hlt, ?_, Or.inr ?_⟩
    · intro x hx
      have hx3 := hsub hx
      obtain ⟨hxJ, -⟩ := hx3
      exact hsub0 hxJ
    · -- Injectivity on the piece via J3.
      intro x hxI hxJ y hyI hyJ hxy
      have hx3J : x ∈ L1J3set M f (openInterval a0 b0) := hsub hxJ
      have hy3J : y ∈ L1J3set M f (openInterval a0 b0) := hsub hyJ
      have hfibxy : ∃ u w : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y u) /\
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x w) /\
          u 0 = w 0 :=
        ⟨(f.toFun ⟨y, hyI⟩).1, (f.toFun ⟨x, hxI⟩).1,
          L1graphMem M f y hyI, L1graphMem M f x hxI,
          (congrArg (fun t => t 0) (congrArg Subtype.val hxy)).symm⟩
      have hfbyx : ∃ u w : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append x u) /\
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (Power.append y w) /\
          u 0 = w 0 :=
        ⟨(f.toFun ⟨x, hxI⟩).1, (f.toFun ⟨y, hyI⟩).1,
          L1graphMem M f x hxI, L1graphMem M f y hyI,
          congrArg (fun t => t 0) (congrArg Subtype.val hxy)⟩
      obtain ⟨hxJ0, -⟩ := hx3J
      obtain ⟨hyJ0, -⟩ := hy3J
      have hx3J' : x ∈ L1J3set M f (openInterval a0 b0) := hsub hxJ
      have hy3J' : y ∈ L1J3set M f (openInterval a0 b0) := hsub hyJ
      have hleft := hChar x hx3J' y hyJ0 hfibxy
      have hright := hChar y hy3J' x hxJ0 hfbyx
      cases hleft with
      | inl h1 =>
          cases hright with
          | inl h2 =>
              have g1 : x 0 < y 0 := h1
              have g2 : y 0 < x 0 := h2
              exact False.elim (lt_irrefl _ (lt_trans g1 g2))
          | inr h2 =>
              have g1 : x 0 < y 0 := h1
              rw [h2] at g1
              exact False.elim (lt_irrefl _ g1)
      | inr heq =>
          cases hright with
          | inl h2 =>
              have g2 : y 0 < x 0 := h2
              rw [heq] at g2
              exact False.elim (lt_irrefl _ g2)
          | inr heq2 =>
              funext i
              have hi0 : i.val = 0 := Nat.lt_one_iff.mp i.isLt
              have hi : i = (0 : Fin 1) := Fin.ext hi0
              rw [hi]
              exact heq
