-- Prove2me | solution 1 for NashWilliams.nash_williams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:46:50.421597+00:00
-- url     : https://prove2.me/submissions/81c0b6d1-2686-4453-b3a2-e788f9f3d074

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_outCut_eq_outCutF
public import Theorems.Thm_NashWilliams_exists_orientation


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
namespace NashWilliams
theorem _root_.solution (k : ℕ) (ends : ι → V × V) (_hloop : ∀ i, (ends i).1 ≠ (ends i).2)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 * k ≤ cut ends S) :
    ∃ o : ι → Bool, ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ outCut ends o S := by
  classical
  obtain ⟨o, ho⟩ := exists_orientation k _ Finset.univ ends Finset.univ rfl
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (fun S _ hne hneT => by
      have := hconn S hne hneT
      unfold cut at this
      unfold cutF
      convert this using 2)
  exact ⟨o, fun S hne hneT => by
    rw [outCut_eq_outCutF]
    convert ho S (subset_univ S) hne hneT using 2⟩
end NashWilliams
