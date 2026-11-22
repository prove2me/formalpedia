-- Prove2me | solution 1 for Monotonicity_Theorem.min_preimage_exists
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:37:55.271567+00:00
-- url     : https://prove2.me/submissions/b8453d2a-1c55-4236-96f3-c50297eb2095

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_exists_least_of_list

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hfinite : forall z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x /\ exists hx : I x, (f.toFun (Subtype.mk x hx)).1 = (fun _ : Fin 1 => z 0))) :
    forall y : Power R 1, (exists x : Power R 1, exists hx : I x,
      (f.toFun (Subtype.mk x hx)).1 = y) ->
      exists m : Power R 1, exists hm : I m,
        (¬ exists w : Power R 1, I w /\ Lt1 D w m /\ exists hxw : I w, exists hxm : I m,
          (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk m hxm)).1) /\
        (f.toFun (Subtype.mk m hm)).1 = y := by
  intro y himg
  obtain ⟨x, hx, hxy⟩ := himg
  have cyeq : (fun _ : Fin 1 => y 0) = y := by
    funext i
    have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
    rw [i0]
  have hfib : (I x ∧ ∃ hx : I x,
      (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => y 0)) := by
    refine ⟨hx, hx, ?_⟩
    exact hxy.trans cyeq.symm
  obtain ⟨LF, hLF⟩ := hfinite y
  have hne : LF ≠ [] := by
    intro hempty
    have hmem : Power.coord1 x ∈ LF := (hLF x).mp hfib
    rw [hempty] at hmem
    exact List.not_mem_nil hmem
  obtain ⟨c, hcM, hcL⟩ := Monotonicity_Theorem.exists_least_of_list D LF hne
  have hcmem : Power.coord1 (fun _ => c) ∈ LF := by
    show c ∈ LF
    exact hcM
  have hfibM := (hLF (fun _ => c)).mpr hcmem
  obtain ⟨hm, hfm⟩ := hfibM
  obtain ⟨hm2, hfm2⟩ := hfm
  have hS : (⟨(fun _ => c), hm2⟩ : {x : Power R 1 // I x})
      = (⟨(fun _ => c), hm⟩ : {x : Power R 1 // I x}) := Subtype.ext rfl
  rw [hS] at hfm2
  have hfm2c : (f.toFun (⟨(fun _ => c), hm⟩ : {x : Power R 1 // I x})).1
      = (fun _ : Fin 1 => y 0) := hfm2
  have hneg : ¬ exists w : Power R 1, I w /\ Lt1 D w (fun _ => c) /\
      exists hxw : I w, exists hxm : I (fun _ => c),
        (f.toFun (Subtype.mk w hxw)).1
          = (f.toFun (Subtype.mk (fun _ => c) hxm)).1 := by
    intro ⟨w, hwI, hlt, hxw, hxmW, heq⟩
    have hWc : (⟨(fun _ => c), hxmW⟩ : {x : Power R 1 // I x})
        = (⟨(fun _ => c), hm⟩ : {x : Power R 1 // I x}) := Subtype.ext rfl
    have hfibW : (I w ∧ ∃ hx : I w,
        (f.toFun ⟨w, hx⟩).1 = (fun _ : Fin 1 => y 0)) := by
      refine ⟨hwI, hxw, ?_⟩
      rw [heq, hWc]
      exact hfm2c
    have hmemW : Power.coord1 w ∈ LF := (hLF w).mp hfibW
    have hlt' : D.lt (Power.coord1 w) c := hlt
    cases hcL (Power.coord1 w) hmemW with
    | inl h => exact D.irrefl c (D.trans h hlt')
    | inr heq2 =>
      rw [heq2] at hlt'
      exact D.irrefl _ hlt'
  refine ⟨(fun _ => c), hm, hneg, ?_⟩
  exact hfm2c.trans cyeq
