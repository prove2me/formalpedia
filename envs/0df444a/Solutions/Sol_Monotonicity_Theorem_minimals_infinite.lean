-- Prove2me | solution 1 for Monotonicity_Theorem.minimals_infinite
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:52:11.905745+00:00
-- url     : https://prove2.me/submissions/7136476c-a5ac-4f1a-af07-be7c5ddc3830

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_infinite_image_of_finite_fibers
import Theorems.Thm_Monotonicity_Theorem_min_preimage_exists

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I)
    (hfinite : forall z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x /\ exists hx : I x, (f.toFun (Subtype.mk x hx)).1 = (fun _ : Fin 1 => z 0))) :
    IsInfinite1 (fun x : Power R 1 => I x /\ ¬ exists w : Power R 1, I w /\ Lt1 D w x /\
      exists hxw : I w, exists hxx : I x,
        (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1) := by
  classical
  have tconst : forall t : Power R 1, t = (fun _ => Power.coord1 t) := by
    intro t
    funext i
    have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
    rw [i0]
    rfl
  have hImg := Monotonicity_Theorem.infinite_image_of_finite_fibers D M f hI hfinite
  have hMin := Monotonicity_Theorem.min_preimage_exists D M f hfinite
  intro ⟨LM, hLM⟩
  apply hImg
  refine ⟨(LM.filter (fun c => decide (exists m : Power R 1,
      (I m ∧ ¬ exists w : Power R 1, I w ∧ Lt1 D w m ∧
        exists hxw : I w, exists hxm : I m,
          (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk m hxm)).1)
      ∧ Power.coord1 m = c))).map
    (fun c => if h : I (fun _ => c) then ((f.toFun ⟨fun _ => c, h⟩).1) 0 else c),
    fun y => ⟨?_, ?_⟩⟩
  · intro hym
    obtain ⟨x, hx, hxy⟩ := hym
    obtain ⟨m, hm, hneg, hfm⟩ := hMin _ ⟨x, hx, hxy⟩
    have hminM : (I m ∧ ¬ exists w : Power R 1, I w ∧ Lt1 D w m ∧
        exists hxw : I w, exists hxm : I m,
          (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk m hxm)).1) :=
      ⟨hm, hneg⟩
    have hcm : Power.coord1 m ∈ LM := (hLM m).mp hminM
    have hmc : m = (fun _ => Power.coord1 m) := tconst m
    have hPc : (∃ m' : Power R 1, (I m' ∧ ¬ exists w : Power R 1, I w ∧ Lt1 D w m' ∧
        exists hxw : I w, exists hxm : I m',
          (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk m' hxm)).1)
        ∧ Power.coord1 m' = Power.coord1 m) := ⟨m, hminM, rfl⟩
    have hmemF : (Power.coord1 m) ∈ LM.filter (fun c => decide (∃ m' : Power R 1,
        (I m' ∧ ¬ exists w : Power R 1, I w ∧ Lt1 D w m' ∧
          exists hxw : I w, exists hxm : I m',
            (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk m' hxm)).1)
        ∧ Power.coord1 m' = c)) := by
      rw [List.mem_filter]
      exact ⟨hcm, by rw [decide_eq_true_eq]; exact hPc⟩
    have hIcon : I (fun _ => Power.coord1 m) := by
      rw [← hmc]
      exact hm
    rw [List.mem_map]
    refine ⟨Power.coord1 m, hmemF, ?_⟩
    show (if h : I (fun _ => Power.coord1 m) then
        ((f.toFun ⟨fun _ => Power.coord1 m, h⟩).1) 0 else Power.coord1 m)
      = Power.coord1 y
    rw [dif_pos hIcon]
    have hSub : (⟨(fun _ => Power.coord1 m), hIcon⟩ : {x : Power R 1 // I x})
        = (⟨m, hm⟩ : {x : Power R 1 // I x}) := Subtype.ext hmc.symm
    calc ((f.toFun (⟨(fun _ => Power.coord1 m), hIcon⟩ : {x : Power R 1 // I x})).1) 0
        = ((f.toFun (⟨m, hm⟩ : {x : Power R 1 // I x})).1) 0 := by rw [hSub]
      _ = Power.coord1 y := by
        rw [hfm]
        rfl
  · intro hyl
    rw [List.mem_map] at hyl
    obtain ⟨c, hcF, hFc⟩ := hyl
    rw [List.mem_filter, decide_eq_true_eq] at hcF
    obtain ⟨hcLM, hPc⟩ := hcF
    obtain ⟨m, hminM, hcm⟩ := hPc
    have hmI : I m := hminM.1
    have hmc : m = (fun _ => c) := by
      rw [tconst m, hcm]
    have hIcon : I (fun _ => c) := by
      rw [← hmc]
      exact hmI
    rw [dif_pos hIcon] at hFc
    have hY : y = (f.toFun (⟨(fun _ => c), hIcon⟩ : {x : Power R 1 // I x})).1 := by
      have t1 : y = (fun _ => Power.coord1 y) := tconst y
      have t2 : (fun _ : Fin 1 => Power.coord1 y)
          = (f.toFun (⟨(fun _ => c), hIcon⟩ : {x : Power R 1 // I x})).1 := by
        funext i
        have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
        rw [i0]
        show Power.coord1 y
          = ((f.toFun (⟨(fun _ => c), hIcon⟩ : {x : Power R 1 // I x})).1)
            ((⟨0, by omega⟩ : Fin 1))
        exact hFc.symm
      exact t1.trans t2
    exact ⟨(fun _ => c), hIcon, hY.symm⟩
