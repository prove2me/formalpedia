-- Prove2me | solution 1 for Hintz2026.Dm_g1
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:55:13.930052+00:00
-- url     : https://prove2.me/submissions/8977ff69-e418-47dc-9282-423344f38fae

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_Dm_div_sqrtDel

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) : Dm p (g1 p e F) x = Dm p F.psi2 x + (↑e * I) * (Dm p F.psi1 x / ↑(Real.sqrt (Del p (x 0))) - F.psi1 x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0)))) :=
  by
    rw [g1_eq, Dm_add p _ _ x (hF.psi2 0) (diff_const_mul_slice _ (fun z => F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.psi1 hF.psi1) 0)
          (hF.psi2 1) (diff_const_mul_slice _ (fun z => F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.psi1 hF.psi1) 1),
        Dm_const_mul, Dm_div_sqrtDel p hx F.psi1 hF.psi1]

end
