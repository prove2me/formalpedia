-- Prove2me | solution 1 for Matrix.aeval_const_term_eq_zero_of_forall_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/95197a3e-acfc-5910-9008-dc079c5b66ee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_aeval_const_term_eq_zero_of_forall_pos

namespace P2mAevalConstTerm

open Polynomial

theorem pencil_at_zero {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ) :
    (∑ a : Fin (d + 1), (((0 : ℝ) : ℂ) ^ (a : ℕ)) • M a) = M 0 := by
  rw [Fin.sum_univ_succ]
  simp

theorem continuous_pencil_aeval {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ)
    (q : Polynomial ℂ) :
    Continuous fun y : ℝ =>
      Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q := by
  have hsum : Continuous fun y : ℝ => ∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a := by
    refine continuous_finsetSum _ fun a _ => ?_
    exact ((Complex.continuous_ofReal.pow _).smul continuous_const)
  exact q.continuous_aeval.comp hsum

end P2mAevalConstTerm

open Polynomial in
theorem solution
    {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q = 0) :
    Polynomial.aeval (M 0) q = 0 := by

  set F : ℝ → Matrix (Fin R) (Fin R) ℂ :=
    fun y => Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q with hF
  have hcont : Continuous F := P2mAevalConstTerm.continuous_pencil_aeval M q
  have hclosed : IsClosed (F ⁻¹' {0}) := isClosed_singleton.preimage hcont
  have hsub : Set.Ioi (0 : ℝ) ⊆ F ⁻¹' {0} := fun y hy => h y hy
  have hcl : closure (Set.Ioi (0 : ℝ)) ⊆ F ⁻¹' {0} := hclosed.closure_subset_iff.mpr hsub
  have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact Set.self_mem_Ici
  have hF0 : F 0 = 0 := hcl h0

  have : F 0 = Polynomial.aeval (M 0) q := by
    simp only [hF]
    rw [P2mAevalConstTerm.pencil_at_zero M]
  rw [← this]
  exact hF0

end S_Matrix_aeval_const_term_eq_zero_of_forall_pos
end P2MW
export P2MW.S_Matrix_aeval_const_term_eq_zero_of_forall_pos (solution)
