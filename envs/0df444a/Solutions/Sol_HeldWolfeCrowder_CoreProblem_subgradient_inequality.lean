-- Prove2me | solution 1 for HeldWolfeCrowder.CoreProblem.subgradient_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:18:44.129534+00:00
-- url     : https://prove2.me/submissions/8c8aef18-7f4d-4095-8d45-79049fb3134c

import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting

namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

theorem aux_sgi_w_le {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (π : EuclideanSpace ℝ (Fin n)) (k : ι) :
    w c v π ≤ c k + ⟪π, v k⟫_ℝ := by
  unfold w
  exact Finset.inf'_le (fun k => c k + ⟪π, v k⟫_ℝ) (Finset.mem_univ k)

end HeldWolfeCrowder.CoreProblem

open HeldWolfeCrowder.CoreProblem
open scoped InnerProductSpace
open Filter Topology

theorem solution {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n))
    (πstar : EuclideanSpace ℝ (Fin n)) (hstar : ∀ π', w c v π' ≤ w c v πstar)
    (π : EuclideanSpace ℝ (Fin n)) (k : ι) (hk : IsMinIndex c v π k) :
    w c v πstar - w c v π ≤ ⟪v k, πstar - π⟫_ℝ := by
  have h1 := aux_sgi_w_le c v πstar k
  unfold IsMinIndex at hk
  rw [← hk, inner_sub_right, real_inner_comm πstar (v k), real_inner_comm π (v k)]
  linarith
