-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_recs_slots_lt_NR_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:39:58.778123+00:00
-- url     : https://prove2.me/submissions/1fc61336-a40a-4df6-b6aa-579e8bffad62

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

/-!
# recs_slots_lt_NR_rec — chunked GREC `List.all` / `decide` certificate on QHNetRec

`chunkDec` is the total `Nat.rec` decoder in `BitOppbankQHNetRec`. One `decide` over
`GREC.all (fun x => (chunkDec x).all recOk)` covers all densified chunks
(no `native_decide`).
-/

open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.LocGrecDense
open IntMul.Kappa.R8.Bit.Oppbank (NR)

private def recOk (r : Rec) : Bool :=
  decide
    (r.2.1 < 27794 ∧ (r.2.2.1 = 0 ∨ r.2.2.1 - 1 < 27794) ∧ ∀ o ∈ r.2.2.2, o < 27794)

private theorem grec_chunks_recOk :
    GREC.all (fun x => (chunkDec x).all recOk) = true := by
  decide

theorem solution :
    ∀ r ∈ recs, r.2.1 < NR ∧ (r.2.2.1 = 0 ∨ r.2.2.1 - 1 < NR) ∧ ∀ o ∈ r.2.2.2, o < NR := by
  intro r hr
  have hall := grec_chunks_recOk
  simp only [recs, List.mem_flatMap] at hr
  obtain ⟨x, hx, hrx⟩ := hr
  have hxok : (chunkDec x).all recOk = true := (List.all_eq_true.1 hall) x hx
  have hbool : recOk r = true := (List.all_eq_true.1 hxok) r hrx
  have hprop :
      r.2.1 < 27794 ∧ (r.2.2.1 = 0 ∨ r.2.2.1 - 1 < 27794) ∧ ∀ o ∈ r.2.2.2, o < 27794 :=
    of_decide_eq_true (by simpa [recOk] using hbool)
  simpa [NR] using hprop
