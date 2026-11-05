-- Prove2me | solution 2 for GeneralPieces.Series.cfP_epsP_pow
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:33:22.263526+00:00
-- url     : https://prove2.me/submissions/1a0cf925-9fcd-49b0-b6c9-3f354aff3530

import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_GeneralPieces_Series_cf_diag
import Theorems.Thm_GeneralPieces_Series_cf_one
import Theorems.Thm_GeneralPieces_Series_eps_pow_succ

set_option autoImplicit false

section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ}

theorem solution (N : ℕ) : cfP (epsP ^ N) (-(N : ℤ)) 0 = 1 := by
  rw [cfP, epsP]
  rcases N with _ | N
  · rw [pow_zero, cf_one]
    simp
  · rw [eps_pow_succ, cf_diag, if_pos ⟨le_refl _, by push_cast; ring⟩]
    simp
