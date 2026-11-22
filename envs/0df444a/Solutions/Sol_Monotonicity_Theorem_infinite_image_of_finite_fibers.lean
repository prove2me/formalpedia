-- Prove2me | solution 1 for Monotonicity_Theorem.infinite_image_of_finite_fibers
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:06:48.439316+00:00
-- url     : https://prove2.me/submissions/03d9b45c-2191-48ea-8b92-3e96bba28dc4

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I)
    (hfinite : forall z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x /\ exists hx : I x, (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0))) :
    IsInfinite1 (fun y : Power R 1 => exists x : Power R 1, exists hx : I x,
      (f.toFun (Subtype.mk x hx)).1 = y) := by
  intro hImg
  apply hI
  obtain ⟨LY, hLY⟩ := hImg
  let fiberList : Power R 1 -> List R := fun z => Classical.choose (hfinite z)
  have fiberSpec : forall z x, ((I x /\ exists hx : I x,
      (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0))
      <-> Power.coord1 x ∈ fiberList z) :=
    fun z x => Classical.choose_spec (hfinite z) x
  refine ⟨LY.flatMap (fun r => fiberList (fun _ => r)), fun x => ⟨fun hxI => ?_, fun hxM => ?_⟩⟩
  · set r : R := Power.coord1 ((f.toFun (⟨x, hxI⟩ : {x : Power R 1 // I x})).1) with hr
    have hrLY : r ∈ LY := by
      have hmem : (fun y : Power R 1 => exists x : Power R 1, exists hx : I x,
          (f.toFun (Subtype.mk x hx)).1 = y)
          ((f.toFun (⟨x, hxI⟩ : {x : Power R 1 // I x})).1) :=
        ⟨x, hxI, rfl⟩
      have hcoord := (hLY _).mp hmem
      simpa [hr] using hcoord
    have hmem : Power.coord1 x ∈ fiberList (fun _ => r) := by
      apply (fiberSpec (fun _ => r) x).mp
      refine ⟨hxI, hxI, ?_⟩
      funext i
      have hi : i.val < 1 := i.isLt
      have hv : i.val = 0 := by omega
      have heqi : i = (0 : Fin 1) := Fin.ext hv
      rw [heqi]
      rfl
    exact List.mem_flatMap.mpr ⟨r, hrLY, hmem⟩
  · obtain ⟨r, _, hrM⟩ := List.mem_flatMap.mp hxM
    exact ((fiberSpec (fun _ => r) x).mpr hrM).1
