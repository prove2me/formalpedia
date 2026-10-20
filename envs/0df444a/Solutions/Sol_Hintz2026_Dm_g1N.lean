-- Prove2me | solution 1 for Hintz2026.Dm_g1N
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:55:15.834978+00:00
-- url     : https://prove2.me/submissions/ad5e1e75-e132-4cb0-9160-804a186b176e

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_Dm_sqrtDel_mul

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) : Dm p (g1N p e G) x = Dm p G.psim2 x + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dm p G.psim1 x + ↑(Del' p (x 0)) / 2 * G.psim1 x) :=
  by
    rw [g1N_eq, Dm_add p _ _ x (hG.psim2 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 0)
          (hG.psim2 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 1),
        Dm_const_mul, Dm_sqrtDel_mul p hx G.psim1 hG.psim1]

end
