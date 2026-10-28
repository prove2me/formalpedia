-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Pnd_Pl_idem
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:43:16.465984+00:00
-- url     : https://prove2.me/submissions/4963f899-c52a-4f02-9291-4122e8fdf230

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

private theorem Pl_eq_ProjB (T : ℕ) : Pl T = ProjB.Pl T := by
  unfold Pl ProjB.Pl xv ProjB.xv yv ProjB.yv tvQ ProjB.tvQ
  unfold triL ProjB.tri ptsL ProjB.pts fieldOf ProjB.fieldOf
  rfl

theorem solution {T : ℕ} (hT : T < v) : Pl T * Pl T = Pl T := by
  have h1771 : T < 1771 := by
    simpa [IntMul.Kappa.R8.Bit.Oppbank.v] using hT
  rw [Pl_eq_ProjB T]
  exact NetFB.Pl_idem h1771
