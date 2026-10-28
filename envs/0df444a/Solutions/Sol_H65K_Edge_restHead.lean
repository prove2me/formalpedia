-- Prove2me | solution 1 for H65K.Edge.restHead
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:34:07.935858+00:00
-- url     : https://prove2.me/submissions/9b4cb3cf-0f37-44fd-ad0d-1308c8523143

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    (Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) &&
      eqB (E.x E.m) (ofInt (-1)) &&
      (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
      eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1))) = true := by
  decide +kernel
