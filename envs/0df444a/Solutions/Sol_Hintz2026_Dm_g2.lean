-- Prove2me | solution 1 for Hintz2026.Dm_g2
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:55:17.826006+00:00
-- url     : https://prove2.me/submissions/34d4ade0-9435-454a-9e5e-9787c136d7a2

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_Dm_div_sqrtDel

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) : Dm p (g2 p e F) x = (-2 * ↑p.Q) * (Dm p F.k x + (↑e * I) * (Dm p F.s x / ↑(Real.sqrt (Del p (x 0))) - F.s x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0))))) :=
  by
    rw [g2_eq, Dm_const_mul, Dm_add p _ _ x (hF.k 0) (diff_const_mul_slice _ (fun z => F.s z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.s hF.s) 0)
          (hF.k 1) (diff_const_mul_slice _ (fun z => F.s z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.s hF.s) 1),
        Dm_const_mul, Dm_div_sqrtDel p hx F.s hF.s]

end
