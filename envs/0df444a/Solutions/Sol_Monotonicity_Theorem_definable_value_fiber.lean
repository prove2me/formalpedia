-- Prove2me | solution 1 for Monotonicity_Theorem.definable_value_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:06:46.399091+00:00
-- url     : https://prove2.me/submissions/e40e3e04-ecef-4dc4-afaa-72aeff5ad8b3

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

namespace Monotonicity_Theorem

theorem left_append_aux {R : Type} (x : Power R 1) (y : Power R 1) :
    Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem right_append_aux {R : Type} (x : Power R 1) (y : Power R 1) :
    Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y := by
  funext j
  exact Fin.append_right x y j

end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (z : Power R 1) :
    M.S 1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
      (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)) := by
  have hSingle : M.S 1 (pointSet (R := R) (z 0)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point (z 0))
  have hProd : M.S (1 + 1)
      (fun p : Power R (1 + 1) =>
        I (Power.left p) ∧ (pointSet (R := R) (z 0)) (Power.right p)) :=
    M.product_mem f.domain_mem hSingle
  have hInter : M.S (1 + 1)
      (setInter (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)
        (fun p : Power R (1 + 1) =>
          I (Power.left p) ∧ (pointSet (R := R) (z 0)) (Power.right p))) :=
    M.inter_mem f.graph_mem hProd
  have hProj : M.S 1
      (fun x : Power R 1 => ∃ y : Power R 1,
        setInter (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)
          (fun p : Power R (1 + 1) =>
            I (Power.left p) ∧ (pointSet (R := R) (z 0)) (Power.right p))
          (Power.append x y)) :=
    M.existsLast_mem hInter
  have heq : (fun x : Power R 1 => ∃ y : Power R 1,
        setInter (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)
          (fun p : Power R (1 + 1) =>
            I (Power.left p) ∧ (pointSet (R := R) (z 0)) (Power.right p))
          (Power.append x y))
      = (fun x : Power R 1 => I x ∧ ∃ hx : I x,
        (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)) := by
    funext x
    apply propext
    constructor
    · intro ⟨y, hG, hI, hZ⟩
      obtain ⟨hx0, hEq0⟩ := hG
      have eL : Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x :=
        left_append_aux x y
      have eR : Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y :=
        right_append_aux x y
      have hx : I x := by rw [← eL]; exact hx0
      have hSub : (⟨Power.left (Power.append x y), hx0⟩ : {x : Power R 1 // I x})
          = (⟨x, hx⟩ : {x : Power R 1 // I x}) := Subtype.ext eL
      have hEq1 : (Power.right (Power.append x y) : Power R 1)
          = ((f.toFun (⟨Power.left (Power.append x y), hx0⟩ : {x : Power R 1 // I x})).1
            : Power R 1) := hEq0
      have hEq2 : y = ((f.toFun (⟨x, hx⟩ : {x : Power R 1 // I x})).1 : Power R 1) := by
        have h1 : (Power.right (Power.append x y) : Power R 1)
            = ((f.toFun (⟨x, hx⟩ : {x : Power R 1 // I x})).1 : Power R 1) := by
          rw [hSub] at hEq1
          exact hEq1
        rw [← eR]
        exact h1
      have hZ' : y 0 = z 0 := by
        have h1 : (Power.right (Power.append x y) : Power R 1) 0 = z 0 := hZ
        rw [eR] at h1
        exact h1
      refine ⟨hx, hx, ?_⟩
      have hy0 : (((f.toFun (⟨x, hx⟩ : {x : Power R 1 // I x})).1 : Power R 1)) 0
          = z 0 := by
        rw [← hEq2]
        exact hZ'
      funext i
      have hi : i.val < 1 := i.isLt
      have hv : i.val = 0 := by omega
      have heqi : i = (0 : Fin 1) := Fin.ext hv
      rw [heqi]
      exact hy0
    · intro ⟨hxI, hx, hEq⟩
      set y0 : Power R 1 := ((f.toFun (⟨x, hx⟩ : {x : Power R 1 // I x})).1
        : Power R 1) with hy0def
      have eL : Power.left (R := R) (n := 1) (m := 1) (Power.append x y0) = x :=
        left_append_aux x y0
      have eR : Power.right (R := R) (n := 1) (m := 1) (Power.append x y0) = y0 :=
        right_append_aux x y0
      refine ⟨y0, ?_, ?_, ?_⟩
      · have hWit : I (Power.left (Power.append x y0)) := by
          rw [eL]
          exact hxI
        have hSub2 : (⟨x, hx⟩ : {x : Power R 1 // I x})
            = (⟨Power.left (Power.append x y0), hWit⟩
              : {x : Power R 1 // I x}) := Subtype.ext eL.symm
        have hEqW : Power.right (Power.append x y0)
            = ((f.toFun (⟨Power.left (Power.append x y0), hWit⟩
              : {x : Power R 1 // I x})).1 : Power R 1) := by
          rw [eR, ← hSub2]
        exact ⟨hWit, hEqW⟩
      · have : I (Power.left (Power.append x y0)) := by
          rw [eL]
          exact hxI
        exact this
      · show (Power.right (Power.append x y0) : Power R 1) 0 = z 0
        rw [eR]
        have hEq' : y0 = (fun _ : Fin 1 => z 0) := hEq
        rw [hEq']
  rw [heq] at hProj
  exact hProj
