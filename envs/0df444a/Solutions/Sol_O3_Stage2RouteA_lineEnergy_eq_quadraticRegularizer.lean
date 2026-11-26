-- Prove2me | solution 1 for O3.Stage2RouteA.lineEnergy_eq_quadraticRegularizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:17.458577+00:00
-- url     : https://prove2.me/submissions/72ccb0fa-335b-44fb-a789-ca71b30cda21

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_lpNorm_sq_eq_lpPower_rpow

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    lineEnergy p x h t = quadraticRegularizer p 0 (x + t • h) := by
  rw [lineEnergy, quadraticRegularizer, sub_zero, lpNorm_sq_eq_lpPower_rpow hp]
  rfl
end O3.Stage2RouteA
