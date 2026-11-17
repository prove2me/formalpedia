-- Prove2me | solution 1 for N25.unitOrders25_annihilator_certificate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:34.190952+00:00
-- url     : https://prove2.me/submissions/f815f02b-c536-4311-b4f3-ad496832350f

import Mathlib
import Definitions.Def_N25_UnitOrders

set_option autoImplicit false

namespace N25

theorem _root_.solution :
    let C : Fin 5 → Fin 5 → ℤ :=
      ![![0,0,0,0,0], ![12,1,17,26,0], ![1,6,31,14,0],
        ![17,31,30,25,0], ![26,14,25,9,0]]
    ∀ i j k : Fin 5,
      (∑ r : Fin 5, (C j r-C i r)*unitOrders25 r k) =
        71*((if k=i then 1 else 0)-(if k=j then 1 else 0)) := by decide

end N25
