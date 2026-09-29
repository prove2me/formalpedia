-- Prove2me | solution 1 for LiuPass.Kt_le_length_add_const
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:23:41.592999+00:00
-- url     : https://prove2.me/submissions/d35e5980-b184-4d56-b731-bb03431ac09f

import Mathlib
import Definitions.Def_LiuPass_crypto

set_option autoImplicit false

open Finset
open scoped Classical

open LiuPass in
theorem solution (U : UMachine) :
    ∃ c : ℕ, ∀ t : ℕ → ℕ, (∀ n, 0 < t n) → ∀ x : BitStr, Kt U t x ≤ x.length + c := by
  refine ⟨U.idProg.length + U.pairOverhead, fun t ht x => ?_⟩
  have hrun : U.run (U.pair U.idProg x) (t x.length) = some x :=
    U.run_idProg x (t x.length) (ht x.length)
  have hle : Kt U t x ≤ (U.pair U.idProg x).length :=
    Nat.sInf_le ⟨U.pair U.idProg x, rfl, hrun⟩
  have hlen := U.pair_length_le U.idProg x
  omega
