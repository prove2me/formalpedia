-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_PT
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:24:44.374254+00:00
-- url     : https://prove2.me/submissions/c31bd3aa-218b-42a1-9cec-3af940764732

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R6_Defs20
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Matrix
open NetLabels
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private theorem rank_idem {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (h : P * P = P) :
    (P.rank : ℚ) = P.trace :=
  NetLabels.rank_eq_trace_of_idem P h

private theorem Pl_eq_ProjB (T : ℕ) : Pl T = ProjB.Pl T := rfl

private theorem Pl_rank {T : ℕ} (hT : T < 1771) : (Pl T).rank = 1 := by
  rw [Pl_eq_ProjB]
  have := rank_idem (Pl_idem hT)
  rw [ProjB.Pl, Matrix.trace_vecMulVec, dotProduct_comm, yx hT] at this
  exact_mod_cast this

private theorem compl_rank {T : ℕ} (hT : T < 1771) : (1 - Pl T).rank = 22 := by
  have hidem : Pl T * Pl T = Pl T := by
    rw [Pl_eq_ProjB]; exact Pl_idem hT
  have := rank_idem (one_sub_idem hidem)
  rw [Matrix.trace_sub, Matrix.trace_one, ← rank_idem hidem, Pl_rank hT] at this
  simp at this
  norm_num at this
  exact_mod_cast this

theorem solution {c : ℕ} (h2 : 2 ≤ c) (hPT : c < 1773) :
    (Pc c).rank = 22 := by
  have hP : Pc c = 1 - Pl (c - 2) := by
    simp [Pc, show c ≠ 0 by omega, show c ≠ 1 by omega, hPT]
  rw [hP]
  exact compl_rank (by omega)
