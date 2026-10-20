-- Prove2me | solution 1 for Hintz2026.Cmat_mul_Xstar
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T14:56:11.945602+00:00
-- url     : https://prove2.me/submissions/9797f901-fdf1-418d-ac34-9c06d868c8a8

import Definitions.Def_Hintz2026_System4

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x * (X p x)ᴴ = adjugate (X p x) * (cscalar p sg om mm x • 1 - Bmat p sg om mm x) :=
  by
    unfold Cmat
    rw [Matrix.smul_mul, Matrix.mul_assoc, inv_mul_Xstar p hx, Matrix.mul_one,
      ← Matrix.smul_mul, detX_Xinv_eq_adj p hx]

end
