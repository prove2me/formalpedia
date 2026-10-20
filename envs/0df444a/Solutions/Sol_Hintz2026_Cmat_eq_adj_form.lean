-- Prove2me | solution 1 for Hintz2026.Cmat_eq_adj_form
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T14:56:14.245883+00:00
-- url     : https://prove2.me/submissions/9d6e282f-9b3d-4c5f-a852-d26b50f0b618

import Definitions.Def_Hintz2026_System4

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ • (adjugate (X p x) * (cscalar p sg om mm x • 1 - Bmat p sg om mm x) * (adjugate (X p x))ᴴ) :=
  by
    unfold Cmat
    rw [Xstar_inv_eq p hx, Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul,
      ← Matrix.smul_mul, ← Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, detX_Xinv_eq_adj p hx]

end
