-- Prove2me | solution 1 for Monotonicity_Theorem.const_cont_of_const
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-14T23:21:37.897954+00:00
-- url     : https://prove2.me/submissions/a21ccd91-1678-4393-a6a4-5c9e5a12c36a

import Definitions.Def_Monotonicity_Theorem_Framework2
import Mathlib.Tactic.FinCases

open Classical
open Monotonicity_Theorem

namespace Monotonicity_Theorem

-- Points are determined by coordinates (inlined from DiscTower: that module
-- cannot be imported alongside Framework2 on the server).
theorem ptLam {R : Type} (x : Power R 1) : x = fun _ => Power.coord1 x := by
  funext k
  have hk : k.val = 0 := by
    have := k.isLt
    omega
  have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
  rw [ek]
  rfl

end Monotonicity_Theorem

theorem solution {R : Type} [LinearOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (lo hi : R)
    (hsub : ∀ x : Power R 1, openInterval (Endpoint.finite lo) (Endpoint.finite hi) x → I x)
    (hconst : ∀ x (hxI : I x), openInterval (Endpoint.finite lo) (Endpoint.finite hi) x →
      ∀ y (hyI : I y), openInterval (Endpoint.finite lo) (Endpoint.finite hi) y →
      (f.toFun ⟨x, hxI⟩).1 = (f.toFun ⟨y, hyI⟩).1) :
    (openInterval (Endpoint.finite lo) (Endpoint.finite hi)).Subset
      (ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  intro x hJx
  have hxI : I x := hsub x hJx
  refine ⟨hxI, ?_⟩
  intro w₀ hG ε₁ ε₂ he₁ he₂
  have hlo_x : LT.lt lo (Power.coord1 x) := hJx.left
  have hx_hi : LT.lt (Power.coord1 x) hi := hJx.right
  refine ⟨lo, hi, hlo_x, hx_hi, ?_⟩
  intro y v hyI hGy hdy1 hdy2
  have hyJ : openInterval (Endpoint.finite lo) (Endpoint.finite hi) (fun _ : Fin 1 => y) :=
    ⟨hdy1, hdy2⟩
  have hxI2 : I (fun _ : Fin 1 => Power.coord1 x) := by
    have e : (fun _ : Fin 1 => Power.coord1 x) = x := (ptLam x).symm
    rw [e]
    exact hxI
  have eXY : (f.toFun ⟨fun _ : Fin 1 => y, hyI⟩).1 = (f.toFun ⟨x, hxI⟩).1 :=
    (hconst x hxI hJx (fun _ : Fin 1 => y) hyI hyJ).symm
  have eX : (⟨x, hxI⟩ : {x : Power R 1 // I x}) =
      ⟨fun _ : Fin 1 => Power.coord1 x, hxI2⟩ := Subtype.ext (ptLam x)
  have hv0 : v = (((f.toFun ⟨fun _ : Fin 1 => y, hyI⟩).1) 0) := by
    obtain ⟨hx0, heq0⟩ := hGy
    have eL : Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => y) (fun _ : Fin 1 => v)) =
        (fun _ : Fin 1 => y) := by
      funext i
      simp [Power.left, Power.append, Fin.append_left]
    have eR : Power.right (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => y) (fun _ : Fin 1 => v)) =
        (fun _ : Fin 1 => v) := by
      funext j
      fin_cases j
      rfl
    have hsub : (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => y) (fun _ : Fin 1 => v)), hx0⟩ :
        {x : Power R 1 // I x}) =
        (⟨fun _ : Fin 1 => y, hyI⟩ : {x : Power R 1 // I x}) := Subtype.ext eL
    have hWpt : (fun _ : Fin 1 => v) = ((f.toFun ⟨fun _ : Fin 1 => y, hyI⟩).1) := by
      calc (fun _ : Fin 1 => v)
          = Power.right (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => y) (fun _ : Fin 1 => v)) := eR.symm
        _ = ((f.toFun (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => y) (fun _ : Fin 1 => v)), hx0⟩ :
          {x : Power R 1 // I x})).1) := heq0
        _ = ((f.toFun (⟨fun _ : Fin 1 => y, hyI⟩ : {x : Power R 1 // I x})).1) := by rw [hsub]
    exact congrFun hWpt (0 : Fin 1)
  have hw0 : w₀ = (((f.toFun ⟨fun _ : Fin 1 => Power.coord1 x, hxI2⟩).1) 0) := by
    obtain ⟨hx0, heq0⟩ := hG
    have eL : Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => Power.coord1 x) (fun _ : Fin 1 => w₀)) =
        (fun _ : Fin 1 => Power.coord1 x) := by
      funext i
      simp [Power.left, Power.append, Fin.append_left]
    have eR : Power.right (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => Power.coord1 x) (fun _ : Fin 1 => w₀)) =
        (fun _ : Fin 1 => w₀) := by
      funext j
      fin_cases j
      rfl
    have hsub : (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => Power.coord1 x) (fun _ : Fin 1 => w₀)), hx0⟩ :
        {x : Power R 1 // I x}) =
        (⟨fun _ : Fin 1 => Power.coord1 x, hxI2⟩ : {x : Power R 1 // I x}) := Subtype.ext eL
    have hWpt : (fun _ : Fin 1 => w₀) = ((f.toFun ⟨fun _ : Fin 1 => Power.coord1 x, hxI2⟩).1) := by
      calc (fun _ : Fin 1 => w₀)
          = Power.right (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => Power.coord1 x) (fun _ : Fin 1 => w₀)) :=
          eR.symm
        _ = ((f.toFun (⟨Power.left (Power.append (n := 1) (m := 1) (fun _ : Fin 1 => Power.coord1 x) (fun _ : Fin 1 => w₀)), hx0⟩ :
          {x : Power R 1 // I x})).1) := heq0
        _ = ((f.toFun (⟨fun _ : Fin 1 => Power.coord1 x, hxI2⟩ : {x : Power R 1 // I x})).1) := by rw [hsub]
    exact congrFun hWpt (0 : Fin 1)
  have hvw : v = w₀ := by
    calc v = (((f.toFun ⟨fun _ : Fin 1 => y, hyI⟩).1) 0) := hv0
      _ = (((f.toFun ⟨x, hxI⟩).1) 0) := by rw [eXY]
      _ = (((f.toFun ⟨fun _ : Fin 1 => Power.coord1 x, hxI2⟩).1) 0) := by rw [eX]
      _ = w₀ := hw0.symm
  rw [hvw]
  exact ⟨he₁, he₂⟩
