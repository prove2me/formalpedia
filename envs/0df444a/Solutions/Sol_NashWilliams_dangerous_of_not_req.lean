-- Prove2me | solution 1 for NashWilliams.dangerous_of_not_req
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:25:28.924622+00:00
-- url     : https://prove2.me/submissions/a268f782-3ce1-4d58-aa1c-804c4eb5b1f3

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
public import Theorems.Thm_NashWilliams_cutF_split
public import Theorems.Thm_NashWilliams_cr_of_joins

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution [DecidableEq ι] {K : ℕ} {T : Finset V} {s : V} {ends : ι → V × V}
    {F : Finset ι} (hreq : Req K (T.erase s) ends F) {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (hij : i ≠ j) {u v : V} (hJi : Joins s u (ends i)) (hJj : Joins s v (ends j))
    (hfail : ¬ Req K (T.erase s) (Function.update ends i (u, v)) (F.erase j)) :
    ∃ X ⊆ T.erase s, X ≠ T.erase s ∧ u ∈ X ∧ v ∈ X ∧ cutF ends F X ≤ K + 1 := by
  simp only [Req, not_forall, not_le] at hfail
  obtain ⟨S, hST, hne, hneT, hlt⟩ := hfail
  have hs : s ∉ S := fun h => by simpa using hST h
  have e := cutF_split hi hj hij u v S (ends := ends)
  rw [cr_of_joins hJi hs, cr_of_joins hJj hs] at e
  have hK := hreq S hST hne hneT
  refine ⟨S, hST, hneT, ?_, ?_, ?_⟩
  · by_contra hu
    by_cases hv : v ∈ S <;> simp [cr, hu, hv] at e <;> omega
  · by_contra hv
    by_cases hu : u ∈ S <;> simp [cr, hu, hv] at e <;> omega
  · by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [cr, hu, hv] at e <;> omega
end NashWilliams
