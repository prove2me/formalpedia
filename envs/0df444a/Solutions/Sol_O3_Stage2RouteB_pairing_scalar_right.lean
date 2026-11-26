-- Prove2me | solution 1 for O3.Stage2RouteB.pairing_scalar_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:12.079059+00:00
-- url     : https://prove2.me/submissions/642c2f94-1135-4ecf-bc55-383dfc8d0e07

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_pairing_scalar_left
import Theorems.Thm_O3_pairing_comm


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {d : ℕ} (r : ℝ) (a b : Point d) :
    pairing a (fun i ↦ r * b i) = r * pairing a b := by
  rw [pairing_comm, pairing_scalar_left, pairing_comm]
end O3.Stage2RouteB
