-- Prove2me | solution 1 for Hintz2026.Dp_g1N
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:55:23.574978+00:00
-- url     : https://prove2.me/submissions/03a9de27-de13-4c61-890d-a9f5d06091e6

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_Dp_sqrtDel_mul

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) : Dp p (g1N p e G) x = Dp p G.psim2 x + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dp p G.psim1 x + ↑(Del' p (x 0)) / 2 * G.psim1 x) :=
  by
    rw [g1N_eq, Dp_add p _ _ x (hG.psim2 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 0)
          (hG.psim2 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 1),
        Dp_const_mul, Dp_sqrtDel_mul p hx G.psim1 hG.psim1]

end
