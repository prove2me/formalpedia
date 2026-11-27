-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.exists_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:44.502515+00:00
-- url     : https://prove2.me/submissions/d02b1daa-f60b-4d27-84b0-0462a107cda2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_one
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_exists_rel
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_solve_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution [IsAlgClosed k] [FiniteDimensional k V] (he : 0 < e)
    (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V) : ∃ x, φ x - x = z := by
  obtain ⟨m, ⟨c, hrel⟩, -⟩ := exists_rel k (fun i => (⇑φ)^[i] z)
  cases m with
  | zero => exact ⟨0, by simpa using hrel.symm⟩
  | succ n =>
    set P : k[X] := recPoly (p ^ e) c 1 n - X with hP
    have hc1 : P.coeff 1 = -1 := by simp [hP, recPoly_coeff_one he]
    have hdeg : P.degree ≠ 0 := by
      intro h
      rw [Polynomial.eq_C_of_degree_eq_zero h] at hc1
      simp at hc1
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root P hdeg
    have hy' : (recPoly (p ^ e) c 1 n).eval y = y := by
      have := hy.eq_zero
      simp [hP] at this
      exact sub_eq_zero.mp this
    refine ⟨∑ i ∈ range (n + 1), (recPoly (p ^ e) c 1 i).eval y • (⇑φ)^[i] z, ?_⟩
    rw [solve_of_root hφ z n c hrel 1 y hy', one_smul, add_sub_cancel_left]
end GroundTheory.PAdicHodge.SemilinearResidue
