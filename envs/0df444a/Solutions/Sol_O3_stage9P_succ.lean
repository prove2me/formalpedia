-- Prove2me | solution 1 for O3.stage9P_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:47.962355+00:00
-- url     : https://prove2.me/submissions/a562be30-ec3d-4d8d-822f-393b41b793f3

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} (theta : ℕ → ℝ)
    (g : ℕ → Vec d) (k : ℕ) :
    stage9P theta g (k + 1) =
      (1 - 1 / theta k) • stage9P theta g k +
        (1 / theta k) • g k := rfl
end O3
