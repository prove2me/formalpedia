-- Prove2me | solution 1 for Hintz2026.Dm_g2N
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:55:19.876985+00:00
-- url     : https://prove2.me/submissions/b341ed50-c12c-49b3-b9eb-97f5c5145835

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_Dm_sqrtDel_mul

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) : Dm p (g2N p e G) x = (2 * ↑p.Q) * (Dm p G.n x + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dm p G.l x + ↑(Del' p (x 0)) / 2 * G.l x)) :=
  by
    rw [g2N_eq, Dm_const_mul, Dm_add p _ _ x (hG.n 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 0)
          (hG.n 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 1),
        Dm_const_mul, Dm_sqrtDel_mul p hx G.l hG.l]

end
