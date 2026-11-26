-- Prove2me | solution 1 for O3.Stage2RouteB.deriv_squaredLpEnergy_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:04.581359+00:00
-- url     : https://prove2.me/submissions/b59bf200-86f4-4277-b19c-6ced6c98ff23

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_deriv_squaredLpEnergy_line_of_ne
import Theorems.Thm_O3_Stage2RouteB_deriv_squaredLpEnergy_line_of_eq_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    deriv (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) t =
      pairing (dualityMap p (fun i ↦ x i + t * h i)) h := by
  by_cases hxt : (fun i ↦ x i + t * h i) = 0
  · exact deriv_squaredLpEnergy_line_of_eq_zero hp x h t hxt
  · exact deriv_squaredLpEnergy_line_of_ne hp x h t hxt
end O3.Stage2RouteB
