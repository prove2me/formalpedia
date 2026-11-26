-- Prove2me | solution 1 for O3.Stage2RouteD.pairing_powerDualityMap_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:31.753597+00:00
-- url     : https://prove2.me/submissions/44ea341a-c2f3-42e5-8026-c893cc2596ed

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_scalar_powerDuality_self

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ}
    (u : Point d) : pairing (powerDualityMap p u) u = lpPower p u := by
  unfold pairing powerDualityMap lpPower
  apply Finset.sum_congr rfl
  intro i _
  exact scalar_powerDuality_self hp
end O3.Stage2RouteD
