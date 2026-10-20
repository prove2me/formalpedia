-- Prove2me | solution 1 for Hintz2026.Dp_g2N
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:55:27.471977+00:00
-- url     : https://prove2.me/submissions/31a8fdf9-3db5-4e42-8a0a-248cba447e00

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_Dp_sqrtDel_mul

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) : Dp p (g2N p e G) x = (2 * ↑p.Q) * (Dp p G.n x + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dp p G.l x + ↑(Del' p (x 0)) / 2 * G.l x)) :=
  by
    rw [g2N_eq, Dp_const_mul, Dp_add p _ _ x (hG.n 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 0)
          (hG.n 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 1),
        Dp_const_mul, Dp_sqrtDel_mul p hx G.l hG.l]

end
