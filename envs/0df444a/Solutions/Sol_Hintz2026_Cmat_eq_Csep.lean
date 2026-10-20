-- Prove2me | solution 1 for Hintz2026.Cmat_eq_Csep
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:09:41.035983+00:00
-- url     : https://prove2.me/submissions/5f28e288-27a5-4d2a-a4b8-ecc2013a74f9

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_Cmat_00_eq
import Theorems.Thm_Hintz2026_Cmat_01_eq
import Theorems.Thm_Hintz2026_Cmat_10_eq
import Theorems.Thm_Hintz2026_Cmat_11_eq

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x = Csep p sg om mm x :=
  by
    ext i j; fin_cases i <;> fin_cases j
    · exact Cmat_00_eq p sg om mm hx
    · exact Cmat_01_eq p sg om mm hx
    · exact Cmat_10_eq p sg om mm hx
    · exact Cmat_11_eq p sg om mm hx

end
