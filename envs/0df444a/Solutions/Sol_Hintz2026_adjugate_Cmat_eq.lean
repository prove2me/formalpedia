-- Prove2me | solution 1 for Hintz2026.adjugate_Cmat_eq
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T14:59:59.300045+00:00
-- url     : https://prove2.me/submissions/c4e2c31a-f9c9-407e-a8cb-e266fd2509a9

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_Cmat_eq_adj_form

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : adjugate (Cmat p sg om mm x) = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ • ((X p x)ᴴ * (cscalar p sg om mm x • 1 + Bmat p sg om mm x) * X p x) :=
  by
    have hk : ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q_sq_sub_M_sq_ne_zero p
    rw [Cmat_eq_adj_form p sg om mm hx, adjugate_smul, adjugate_mul_distrib, adjugate_mul_distrib,
      adjugate_cI_sub_B _ _ (Bmat_trace_zero p sg om mm x), ← adjugate_conjTranspose,
      adjugate_adjugate _ (by simp)]
    simp only [Fintype.card_fin, Nat.sub_self, pow_zero, one_smul, pow_one, Nat.add_one_sub_one]
    rw [Matrix.mul_assoc]

end
