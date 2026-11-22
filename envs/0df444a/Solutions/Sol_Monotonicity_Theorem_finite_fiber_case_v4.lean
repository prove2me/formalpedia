-- Prove2me | solution 1 for Monotonicity_Theorem.finite_fiber_case_v4
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T20:00:48.300986+00:00
-- url     : https://prove2.me/submissions/24ceb74d-e3b7-4fef-9039-462b43156ce4

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_fiber_minimals_definable
import Theorems.Thm_Monotonicity_Theorem_minimals_infinite
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I)
    (hfinite : ∀ z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x ∧ ∃ hx : I x, (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0))) :
    ∃ a b : Endpoint R, Endpoint.lt D a b ∧
      (openInterval D a b).Subset I ∧
      (∀ x (hxI : I x), openInterval D a b x → ∀ y (hyI : I y), openInterval D a b y →
        f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI) → x = y) := by
  have hMinDef := Monotonicity_Theorem.fiber_minimals_definable D M f
  have hMinInf := Monotonicity_Theorem.minimals_infinite D M f hI hfinite
  obtain ⟨a, b, hab, hSub⟩ :=
    Monotonicity_Theorem.infinite_definable_set_contains_interval D M _ hMinDef hMinInf
  refine ⟨a, b, hab, ?_, ?_⟩
  · intro x hx
    exact (hSub hx).1
  · intro x hxI hxJ y hyI hyJ heq
    have hxM := hSub hxJ
    have hyM := hSub hyJ
    obtain ⟨hxI', hnegx⟩ := hxM
    obtain ⟨hyI', hnegy⟩ := hyM
    rcases D.trichotomy (x 0) (y 0) with ⟨hlt, _, _⟩ | ⟨heq2, _, _⟩ | ⟨hlt, _, _⟩
    · have hltW : Lt1 D x y := hlt
      have eY : (⟨y, hyI⟩ : {x : Power R 1 // I x})
          = (⟨y, hyI'⟩ : {x : Power R 1 // I x}) := Subtype.ext rfl
      rw [eY] at heq
      have heq' : (f.toFun (⟨x, hxI⟩ : {x : Power R 1 // I x})).1
          = (f.toFun (⟨y, hyI'⟩ : {x : Power R 1 // I x})).1 :=
        congrArg Subtype.val heq
      exact False.elim (hnegy ⟨x, hxI, hltW, hxI, hyI', heq'⟩)
    · funext i
      have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
      rw [i0]
      exact heq2
    · have hltW : Lt1 D y x := hlt
      have eX : (⟨x, hxI⟩ : {x : Power R 1 // I x})
          = (⟨x, hxI'⟩ : {x : Power R 1 // I x}) := Subtype.ext rfl
      rw [eX] at heq
      have heq' : (f.toFun (⟨y, hyI⟩ : {x : Power R 1 // I x})).1
          = (f.toFun (⟨x, hxI'⟩ : {x : Power R 1 // I x})).1 :=
        congrArg Subtype.val heq.symm
      exact False.elim (hnegx ⟨y, hyI, hltW, hyI, hxI', heq'⟩)
