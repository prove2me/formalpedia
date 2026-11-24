-- Prove2me | solution 1 for GlobalTheory.GaussUnits.sum_units_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:11.729557+00:00
-- url     : https://prove2.me/submissions/505b5683-1a57-4a6c-9ace-60559d196fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussUnitsNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ComplexConjugate Finset
open GlobalTheory
open GlobalTheory.GaussUnits
variable {R : Type} [CommRing R] [Fintype R]
namespace GlobalTheory.GaussUnits
theorem _root_.solution (m : Ideal R) [DecidablePred (· ∈ m)] [Fintype Rˣ]
    (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (f : R → ℂ) :
    ∑ u : Rˣ, f u = ∑ x, f x - ∑ x, (if x ∈ m then f x else 0) := by
  have h : ∑ u : Rˣ, f u = ∑ x ∈ univ.filter (fun x => ¬ x ∈ m), f x := by
    refine Finset.sum_bij (fun u _ => (u : R)) ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter]
      exact ⟨mem_univ _, (hm u).mp u.isUnit⟩
    · intro a _ b _ h
      exact Units.ext h
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨((hm x).mpr hx.2).unit, mem_univ _, rfl⟩
    · intro u _
      rfl
  rw [h, eq_sub_iff_add_eq, ← Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]
end GlobalTheory.GaussUnits
