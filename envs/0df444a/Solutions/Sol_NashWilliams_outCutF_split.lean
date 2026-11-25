-- Prove2me | solution 1 for NashWilliams.outCutF_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:28:44.242408+00:00
-- url     : https://prove2.me/submissions/df2639b1-b6a4-4b63-9451-2a2e9fb173ae

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation
public import Theorems.Thm_NashWilliams_outCutF_eq_sum
public import Theorems.Thm_NashWilliams_sum_split


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {ends : ι → V × V} {F : Finset ι} {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (hij : i ≠ j) {s u v : V} (o1 : ι → Bool) (S : Finset V) :
    outCutF ends (liftO s ends o1 i j) F S + lv (u, v) (o1 i) S =
      outCutF (Function.update ends i (u, v)) o1 (F.erase j) S +
        lv (ends i) (liftO s ends o1 i j i) S + lv (ends j) (liftO s ends o1 i j j) S := by
  rw [outCutF_eq_sum, outCutF_eq_sum]
  have := sum_split (f := fun l => lv (ends l) (liftO s ends o1 i j l) S)
    (f1 := fun l => lv (Function.update ends i (u, v) l) (o1 l) S) hi hj hij
    (fun l _ hli hlj => by simp [liftO, hli, hlj])
  simpa using this
end NashWilliams
